#![no_std]

//! `no_std` compatible Cave Story Organya Music Player.
//!
//! Partially based on bisqwit's C++ OrgPlay.
//!
//! # Example
//! ```no_run
//! use orgorg::{OrgPlay, OrgPlayBuilder, AssetByRef, interp_impls::Linear};
//!
//! let wavetable: &[u8; 25600] = todo!();
//! let drum: &[u8; 40000] = todo!();
//! let org: &[u8] = todo!();
//!
//! let mut player: OrgPlay<'_, Linear, AssetByRef<'_>> = OrgPlayBuilder::new()
//!     .with_sample_rate(44100)
//!     .with_interpolation(Linear)
//!     .with_asset(wavetable, drum) // Lifetime of them is now tied to AssetByRef<'_>
//!     .build(org) // Lifetime of `org` is now tied to OrgPlay<'_, ..>
//!     .expect("Invalid organya music");
//!
//! let mut buffer = [0.0_f32; 1024];
//! loop {
//!     player.synth_stereo(&mut buffer);
//!     // Do stuffs with buffer
//! }
//! ```
//!
//! For owned [`OrgPlay`], use self-referential struct helpers like
//! [`self_cell`](https://crates.io/crates/self_cell) or [`ouroboros`](https://crates.io/crates/ouroboros).
//! See orgorg-player for example.
//!
//! # How to get data needed for synthesis
//! See orgorg-player project. Run `orgorg-player dump`.
//!
//! # Performance
//! It is fast and does not allocate memory at all. But with following cavests.
//!
//! FPU should be present for maximum performance,
//! since there are lots of single-precision(f32) floating point arithmetic.
//!
//! This crate uses some unsafe to boost the performance.
//! The author tried to ensure correctness but, who knows. Feel free to audit the code.

use core::{cmp, marker::PhantomData, mem::MaybeUninit, ptr::NonNull};

const MASTER_VOLUME: f32 = 1.0 / (1 << 19) as f32;
const DRUM_LEN: [usize; 6] = [5000, 10000, 10000, 1000, 10000, 4000];
const DRUM_OFFSET: [usize; 7] = [0, 5000, 15000, 25000, 26000, 36000, 40000];

// For more cleaner internal code. not for pub.
trait U8SliceExt {
    fn read_i16(&self, offset: usize) -> i16;
    fn read_u16(&self, offset: usize) -> u16;
    fn read_u32(&self, offset: usize) -> u32;
    fn read_i8(&self, offset: usize) -> i8;
}

impl U8SliceExt for [u8] {
    #[inline]
    fn read_i16(&self, offset: usize) -> i16 {
        i16::from_le_bytes(self[offset..offset + 2].try_into().unwrap())
    }
    #[inline]
    fn read_u16(&self, offset: usize) -> u16 {
        u16::from_le_bytes(self[offset..offset + 2].try_into().unwrap())
    }
    #[inline]
    fn read_u32(&self, offset: usize) -> u32 {
        u32::from_le_bytes(self[offset..offset + 4].try_into().unwrap())
    }
    #[inline]
    fn read_i8(&self, offset: usize) -> i8 {
        self[offset] as i8
    }
}

/// Provides Cave Story wavetables and drum samples.
///
/// You don't need to implement this trait to use [`OrgPlay`],
/// as [`OrgPlayBuilder::with_asset`] will use default implementation
/// that holds references to the data.
///
/// But if you want zero-sized provider, use this snippet in your code.
/// ```ignore
/// struct ConstAsset;
///
/// impl CaveStoryAssetProvider for ConstAsset {
///     fn wavetable(&self) -> &[u8; 25600] {
///         include_bytes!("./wavetable.dat")
///     }
///
///     fn drum(&self) -> &[u8; 40000] {
///         include_bytes!("./drums.dat")
///     }
/// }
/// ```
pub trait CaveStoryAssetProvider {
    /// The original `wavetable.dat` file.
    fn wavetable(&self) -> &[u8; 25600];
    /// 6 pxt samples concatenated.
    ///
    /// Order is: fx96, fx97, fx9a, fx98, fx99, fx9b
    fn drum(&self) -> &[u8; 40000];
}

// Internal helper methods.
trait CaveStoryAssetProviderExt {
    unsafe fn get_wavetable(&self, idx: i8) -> &[i8; 256];
    // MUST NOT return empty array.
    unsafe fn get_drum(&self, idx: i8) -> &[i8];
}

impl<T: CaveStoryAssetProvider> CaveStoryAssetProviderExt for T {
    // Safety: 0 <= idx < 100
    #[inline(always)]
    unsafe fn get_wavetable(&self, idx: i8) -> &[i8; 256] {
        debug_assert!((0..100).contains(&idx));
        let idx = idx as usize * 256;
        unsafe {
            let w: &[u8; 256] = self
                .wavetable()
                .get_unchecked(idx..idx + 256)
                .try_into()
                .unwrap_unchecked();
            let w = w as *const [u8; 256] as *const [i8; 256];
            &*w
        }
    }

    // Safety: 0 <= idx < 6
    #[inline(always)]
    unsafe fn get_drum(&self, idx: i8) -> &[i8] {
        debug_assert!((0..6).contains(&idx));
        let idx = idx as usize;
        unsafe {
            let start = *DRUM_OFFSET.get_unchecked(idx);
            let end = *DRUM_OFFSET.get_unchecked(idx + 1);
            let w = self.drum().get_unchecked(start..end);
            core::slice::from_raw_parts(w.as_ptr() as *const i8, w.len())
        }
    }
}

/// Default provider used in [`OrgPlayBuilder::with_asset`]
pub struct AssetByRef<'a>(&'a [u8; 25600], &'a [u8; 40000]);

impl CaveStoryAssetProvider for AssetByRef<'_> {
    #[inline(always)]
    fn wavetable(&self) -> &[u8; 25600] {
        self.0
    }

    #[inline(always)]
    fn drum(&self) -> &[u8; 40000] {
        self.1
    }
}

/// Interpolation for Organya Music synthesis.
pub trait OrgInterpolation {
    /// Interpolate the `wave` from `pos`. **This function is called at audio rate**.
    /// # Safety
    /// Caller must guarantee that
    /// - `wave` is 256-length wavetable or `[1000, 10000]` length pxt sample,
    /// - `pos` is finite value and `0.0 <= pos < wave.len() as f32`.
    ///
    /// These strict requirements can enable more performant code, like [`f32::to_int_unchecked()`].
    unsafe fn interpolate(wave: &[i8], pos: f32) -> f32;
}

/// Builtin [`OrgInterpolation`] implementations.
pub mod interp_impls {
    use super::OrgInterpolation;
    /// Linear Interpolation. Fast.
    pub struct Linear;

    impl OrgInterpolation for Linear {
        // This function is carefully written with profiling and Compiler Explorer in Rust 1.92
        #[inline(always)]
        unsafe fn interpolate(wave: &[i8], pos: f32) -> f32 {
            let len = wave.len();
            // Safety: Caller guarantees that pos is finite, and 0 <= pos < wave.len().
            unsafe {
                // naive `pos % 1.0` is **300% slower**..WTF?
                // `pos - libm::truncf(pos)` is 20% slower.
                // f32::to_int_unchecked is another significant speedup.
                let pos_i = pos.to_int_unchecked::<i32>();
                // Saves one instruction in aarch64.
                core::hint::assert_unchecked(pos_i >= 0);
                let frac = pos - (pos_i as f32);
                // pos.to_int_unchecked::<usize>() is slower than this cast.
                let pos_idx = pos_i as usize;
                let sample1 = *wave.get_unchecked(pos_idx);
                let sample2 = *wave.get_unchecked((pos_idx + 1) % len);
                // The "imprecise" lerp (see Wikipedia Linear Interpolation).
                // Monotonic, and slightly fast over "precise" one.
                sample1 as f32 + ((sample2 as i32) - (sample1 as i32)) as f32 * frac
            }
        }
    }

    /// No Interpolation. Fastest.
    pub struct NoInterp;

    impl OrgInterpolation for NoInterp {
        #[inline(always)]
        unsafe fn interpolate(wave: &[i8], pos: f32) -> f32 {
            // Safety: Caller guarantees that pos is finite, and 0 <= pos < wave.len().
            unsafe {
                // Again, i32 cast is faster than usize.
                let idx = pos.to_int_unchecked::<i32>();
                core::hint::assert_unchecked(idx >= 0);
                *wave.get_unchecked(idx as usize) as f32
            }
        }
    }

    /// Lagrange Interpolation. Slow.
    pub struct Lagrange;

    impl OrgInterpolation for Lagrange {
        #[inline(always)]
        unsafe fn interpolate(wave: &[i8], pos: f32) -> f32 {
            // Safety: Caller guarantees that pos is finite, and 0 <= pos < wave.len().
            unsafe {
                let len = wave.len();
                let pos_i = pos.to_int_unchecked::<i32>();
                core::hint::assert_unchecked(pos_i >= 0);
                let frac = pos - (pos_i as f32);
                let pos = pos_i as usize;
                let s1 = *wave.get_unchecked(if pos == 0 { len - 1 } else { pos - 1 }) as f32;
                let s2 = *wave.get_unchecked(pos) as f32;
                let s3 = *wave.get_unchecked((pos + 1) % len) as f32;
                // Compiler should optimize this branchless, which is faster than (pos + 2) % idx.
                // (pos + 1) % len is already branchless.
                let s4_idx = if pos + 2 == len + 1 {
                    1
                } else if pos + 2 == len {
                    0
                } else {
                    pos + 2
                };
                let s4 = *wave.get_unchecked(s4_idx) as f32;

                let c0 = s2;
                let c1 = s3 - s1 * (1.0 / 3.0) - s2 * (1.0 / 2.0) - s4 * (1.0 / 6.0);
                let c2 = (s1 + s3) * (1.0 / 2.0) - s2;
                let c3 = (s4 - s1) * (1.0 / 6.0) + (s2 - s3) * (1.0 / 2.0);

                ((c3 * frac + c2) * frac + c1) * frac + c0
            }
        }
    }
}

struct Event {
    note: u8,
    length: u8,
    volume: u8,
    panning: u8,
}

struct Instrument<'a, I: OrgInterpolation, const DRUM: bool> {
    // Must be:
    // - If n_events is 0, this pointer can be dangling so never access it
    // - else, this is a start of &'a [u8] with length of n_events * 8
    // Raw pointer to save a usize space over slice here.
    inst_data_ptr: NonNull<u8>,
    tuning: i16,
    // loop_event: Option<i16> is ergonomic but this saves space
    pi_loop_calculated: u8,
    // Supposedly the maximum number of events in a single instrument is 256.
    // Some incompatible(non-standard?) music can exceed that arbitrary limit.
    // So, be lenient here.
    n_events: u16,
    cur_event: u16,
    // TODO: Pre-calculate this value, not on the fly
    loop_event: u16,
    phase_inc: f32,
    phase_acc: f32,
    cur_pan: u8,
    cur_vol: u8,
    // if n_events != 0, must point to valid wave
    wave_idx: i8,
    cur_len: u32,
    _i: PhantomData<I>,
    _a: PhantomData<&'a [u8]>,
}

unsafe impl<'a, I: OrgInterpolation, const DRUM: bool> Send for Instrument<'a, I, DRUM> {}
unsafe impl<'a, I: OrgInterpolation, const DRUM: bool> Sync for Instrument<'a, I, DRUM> {}

impl<'a, I: OrgInterpolation, const DRUM: bool> Instrument<'a, I, DRUM> {
    // Safety: cur_event < n_events
    #[inline]
    unsafe fn get_cur_event_beat(&self) -> u32 {
        debug_assert!(self.cur_event < self.n_events);
        // Safety: See inst_data_ptr field comment
        unsafe {
            self.inst_data_ptr
                .add(self.cur_event as usize * 4)
                .cast()
                .read_unaligned()
        }
    }

    // Safety: cur_event < n_events
    #[inline]
    unsafe fn get_cur_event(&self) -> Event {
        debug_assert!(self.cur_event < self.n_events);
        // Safety: See inst_data_ptr field comment
        unsafe {
            let n_events = self.n_events as usize;
            let inst_ptr = self
                .inst_data_ptr
                .add(n_events * 4 + self.cur_event as usize);
            let note = inst_ptr.read();
            let length = inst_ptr.add(n_events).read();
            let volume = inst_ptr.add(n_events * 2).read();
            let panning = inst_ptr.add(n_events * 3).read();
            Event {
                note,
                length,
                volume,
                panning,
            }
        }
    }

    fn tick(&mut self, (cur_beat, loop_start, samples_per_beat, rate): &(u32, u32, f32, u32)) {
        // There is no official documentation for .org file,
        // and these logics are not designed to handle it as leniently as possible.
        // It assumes that event is sorted by its beat, and no more event after loop_end.
        // But OrgMaker (the only official .org editor) output follows those rule.
        //
        // Unofficial reference
        // https://gist.github.com/fdeitylink/7fc9ddcc54b33971e5f505c8da2cfd28
        if cur_beat == loop_start {
            if self.pi_loop_calculated & 2 == 2 {
                self.cur_event = self.loop_event;
            } else {
                self.loop_event = self.cur_event;
                self.pi_loop_calculated |= 2;
            }
        }
        if self.cur_event >= self.n_events {
            return;
        }
        // Safety: Checked with above code
        let event = unsafe {
            let cur_event_beat = self.get_cur_event_beat();
            if cur_event_beat == *cur_beat {
                self.get_cur_event()
            } else {
                return;
            }
        };
        self.cur_event += 1;
        if event.volume != 255 {
            self.cur_vol = event.volume;
        }
        if event.panning != 255 {
            let left = (12 - event.panning).min(6);
            let right = event.panning.min(6);
            self.cur_pan = (left << 4) | right;
        }
        if event.note != 255 {
            self.phase_acc = 0.0;
            self.cur_len = 0;
            let rate = *rate as f32;
            if DRUM {
                // Safety: See wave_idx field comment
                let wave_len = unsafe { *DRUM_LEN.get_unchecked(self.wave_idx as usize) };
                let phase_inc = (event.note as i32 * 800 + 100) as f32 / rate;
                // This is needed for OrgInterpolation trait invariant.
                // And if this condition is false, then the pitch isn't in RATE at all.
                let in_pitch = phase_inc.is_finite() && (0.0..wave_len as f32).contains(&phase_inc);
                if in_pitch {
                    self.phase_inc = phase_inc;
                    self.cur_len = (wave_len as f32 / phase_inc) as u32;
                }
            } else {
                const FRQ_TABLE: [i32; 12] =
                    [262, 277, 294, 311, 330, 349, 370, 392, 415, 440, 466, 494];
                let freq = FRQ_TABLE[(event.note % 12) as usize];
                let oct = 1 << (5 + (event.note / 12).min(7) as i32);
                let final_freq = (freq * oct) + (self.tuning as i32 - 1000);
                let phase_inc = final_freq as f32 / rate;
                // This is needed for OrgInterpolation trait invariant.
                // And if this condition is false, then the pitch isn't in RATE at all.
                let in_pitch = phase_inc.is_finite() && (0.0..256.0).contains(&phase_inc);
                if in_pitch {
                    self.phase_inc = phase_inc;
                    self.cur_len = if (self.pi_loop_calculated & 1) == 1 {
                        (1024.0 / phase_inc) as u32
                    } else {
                        (event.length as f32 * samples_per_beat) as u32
                    };
                }
            }
        }
    }

    // This function is the critical part of overall performance.
    // Previously, there was val() method that returns a sample value, which was obviously slower.
    // And as expected, fill_buf is ~1.6x faster than individual val() calls
    fn fill_buf<A: CaveStoryAssetProvider, const MONO: bool>(&mut self, buf: &mut [f32], a: &A) {
        if self.cur_len == 0 {
            return;
        }
        // Safety: See wave_idx field comment
        let cur_wave = unsafe {
            if DRUM {
                a.get_drum(self.wave_idx)
            } else {
                a.get_wavetable(self.wave_idx)
            }
        };
        let len = cur_wave.len();
        // Safety: CaveStoryAssetProviderExt never return empty array.
        // This will eliminate "rem by zero" panic code.
        unsafe { core::hint::assert_unchecked(len != 0) }
        let vol = self.cur_vol as i32;
        // Integer multiplication then float cast is slightly faster
        let left = ((self.cur_pan >> 4) as i32 * vol) as f32 * MASTER_VOLUME;
        let right = ((self.cur_pan & 0b00001111) as i32 * vol) as f32 * MASTER_VOLUME;
        let mono = (((self.cur_pan >> 4) + (self.cur_pan & 0b00001111)) as i32 * vol) as f32
            * (MASTER_VOLUME / 2.0);
        let n = if MONO {
            cmp::min(buf.len(), self.cur_len as usize)
        } else {
            cmp::min(buf.len() / 2, self.cur_len as usize)
        };
        let mut pos = self.phase_acc;
        let inc = self.phase_inc;
        for i in 0..n {
            // Safety:
            // CaveStoryAssetProviderExt never return invalid length array.
            // There is check in tick() method that ensures 0 <= phase_inc < len.
            // And at the end of this for loop, pos is wrapped.
            let sample = unsafe {
                debug_assert!(pos.is_finite() && 0.0 <= pos && pos < len as f32);
                I::interpolate(cur_wave, pos)
            };
            // Seems compiler can't prove that no out of bounds will happen here. Interesting.
            unsafe {
                if MONO {
                    *buf.get_unchecked_mut(i) += sample * mono;
                } else {
                    *buf.get_unchecked_mut(i * 2) += sample * left;
                    *buf.get_unchecked_mut(i * 2 + 1) += sample * right;
                }
            }
            // It actually produces audible pitch instability as number builds up.
            // So, naively wrap the value before it becomes too inaccurate.
            // f64 is another naive fix, but best fix is fixed point numbers.
            // And fixed point could improve overall performance as well, especially on hardware without FPU.
            pos += inc;
            if pos >= len as f32 {
                pos -= len as f32;
            }
        }
        self.phase_acc = pos;
        self.cur_len -= n as u32;
    }
}

/// `no_std` compatible Cave Story Organya Music Player.
pub struct OrgPlay<'a, I: OrgInterpolation, A: CaveStoryAssetProvider> {
    // I want to make this integer, but then RATE must be multiple of 1000.
    sample_rate: u32,
    samples_per_beat: f32,
    remaining_samples: f32,
    loop_start: u32,
    loop_end: u32,
    cur_beat: u32,
    wave_ins: [Instrument<'a, I, false>; 8],
    drum_ins: [Instrument<'a, I, true>; 8],
    asset: A,
}

impl<'a, I: OrgInterpolation, A: CaveStoryAssetProvider> OrgPlay<'a, I, A> {
    fn new(asset: A, song: &'a [u8], rate: u32) -> Option<Self> {
        if song.len() < 114 {
            return None;
        }
        if &song[0..6] != b"Org-02" {
            return None;
        }
        let ms_per_beat = song.read_u16(6);
        if ms_per_beat == 0 {
            return None;
        }
        let samples_per_beat = ms_per_beat as f32 * (rate as f32 / 1000.0);
        let loop_start = song.read_u32(10);
        let loop_end = song.read_u32(14);

        let mut offset = 18;
        let mut ins_data_offset = 114;
        let tick_args = &(0, loop_start, samples_per_beat, rate);

        // core::array really needs try_from_fn, or array::try_map
        // Instrument does not allocate anything so no risk of memory leak when early returns.
        let mut wave_ins = [const { MaybeUninit::uninit() }; 8];
        let mut drum_ins = [const { MaybeUninit::uninit() }; 8];

        for val in &mut wave_ins {
            let wave = song.read_i8(offset + 2);
            let valid_wave = (0..100).contains(&wave);

            let n_events = song.read_u16(offset + 4);
            let pi = if song.read_i8(offset + 3) != 0 { 1 } else { 0 };
            let inst_data_ptr = if n_events == 0 {
                NonNull::dangling()
            } else {
                let inst_data =
                    song.get(ins_data_offset..ins_data_offset + n_events as usize * 8)?;
                // Safety: slice is always valid, and bound checked
                unsafe { NonNull::new_unchecked(inst_data.as_ptr() as *mut u8) }
            };
            let mut ret = Instrument {
                inst_data_ptr,
                tuning: song.read_i16(offset),
                pi_loop_calculated: pi,
                n_events: if valid_wave { n_events } else { 0 }, // Must be 0 for invalid wave
                phase_inc: 0.0,
                phase_acc: 0.0,
                cur_pan: 0,
                cur_vol: 0,
                cur_len: 0,
                cur_event: 0,
                loop_event: 0,
                wave_idx: wave,
                _i: PhantomData,
                _a: PhantomData,
            };
            // Initial ticking for beat 0, since synth function will start ticking at beat 1
            ret.tick(tick_args);
            offset += 6;
            ins_data_offset += n_events as usize * 8;
            val.write(ret);
        }
        for val in &mut drum_ins {
            // -1 means there is no corresponding drum effect.
            const DRUM_MAPPING: [i8; 12] = [0, -1, 1, -1, 2, 3, 4, -1, 5, -1, -1, -1];
            let wave = *DRUM_MAPPING
                .get(song.read_i8(offset + 2) as usize)
                .unwrap_or(&-1);

            let n_events = song.read_u16(offset + 4);
            let pi = if song.read_i8(offset + 3) != 0 { 1 } else { 0 };
            let inst_data_ptr = if n_events == 0 {
                NonNull::dangling()
            } else {
                let inst_data =
                    song.get(ins_data_offset..ins_data_offset + n_events as usize * 8)?;
                // Safety: slice is always valid, and bound checked
                unsafe { NonNull::new_unchecked(inst_data.as_ptr() as *mut u8) }
            };
            let mut ret = Instrument {
                inst_data_ptr,
                tuning: song.read_i16(offset),
                pi_loop_calculated: pi,
                n_events: if wave == -1 { 0 } else { n_events }, // Must be 0 for invalid wave
                phase_inc: 0.0,
                phase_acc: 0.0,
                cur_pan: 0,
                cur_vol: 0,
                cur_len: 0,
                cur_event: 0,
                loop_event: 0,
                wave_idx: wave,
                _i: PhantomData,
                _a: PhantomData,
            };
            // Initial ticking for beat 0, since synth function will start ticking at beat 1
            ret.tick(tick_args);
            offset += 6;
            ins_data_offset += n_events as usize * 8;
            val.write(ret);
        }

        // More data after song? Reject.
        if ins_data_offset != song.len() {
            return None;
        }

        Some(Self {
            sample_rate: rate,
            samples_per_beat,
            remaining_samples: samples_per_beat,
            loop_start,
            loop_end,
            cur_beat: 0,
            // Safety: They are all initialized now.
            // TODO: Switch to array_assume_init when it lands
            wave_ins: unsafe {
                core::mem::transmute::<
                    [MaybeUninit<Instrument<'a, I, false>>; 8],
                    [Instrument<'a, I, false>; 8],
                >(wave_ins)
            },
            drum_ins: unsafe {
                core::mem::transmute::<
                    [MaybeUninit<Instrument<'a, I, true>>; 8],
                    [Instrument<'a, I, true>; 8],
                >(drum_ins)
            },
            asset,
        })
    }

    /// Generates 1-channel mono audio data.
    ///
    /// Values can exceed `[-1, 1]` range on some songs.
    pub fn synth_mono(&mut self, buf: &mut [f32]) {
        self.synth_impl::<true>(buf);
    }

    /// Generates stereo interleaved audio data.
    ///
    /// Values can exceed `[-1, 1]` range on some songs.
    /// # Panics
    ///
    /// Panics if `buf.len()` is not multiple of 2.
    pub fn synth_stereo(&mut self, buf: &mut [f32]) {
        self.synth_impl::<false>(buf);
    }

    fn synth_impl<const MONO: bool>(&mut self, buf: &mut [f32]) {
        if !MONO {
            assert!(buf.len().is_multiple_of(2));
        }
        buf.fill(0.0);
        let mut filled_raw = 0;
        while filled_raw < buf.len() {
            if self.remaining_samples <= 0.0 {
                self.remaining_samples += self.samples_per_beat;
                self.cur_beat += 1;
                if self.cur_beat == self.loop_end {
                    self.cur_beat = self.loop_start;
                }
                // Since they don't change, making and passing a reference to the tuple is
                // slightly faster than 4 individual arguments.
                let tick_args = &(
                    self.cur_beat,
                    self.loop_start,
                    self.samples_per_beat,
                    self.sample_rate,
                );
                for w in &mut self.wave_ins {
                    w.tick(tick_args);
                }
                for w in &mut self.drum_ins {
                    w.tick(tick_args);
                }
            }
            let from_raw = filled_raw;
            // Seems compiler can't treat channel as const and optimize here.
            // let channel = if MONO { 1 } else { 2 };
            //
            // let to_fill_raw = cmp::min(
            //     libm::ceilf(self.remaining_samples) as usize * channel,
            //     buf.len() - filled_raw,
            // );
            // So, manual branching here.
            let to_fill_raw = if MONO {
                cmp::min(
                    libm::ceilf(self.remaining_samples) as usize,
                    buf.len() - filled_raw,
                )
            } else {
                cmp::min(
                    libm::ceilf(self.remaining_samples) as usize * 2,
                    buf.len() - filled_raw,
                )
            };
            // Seems compiler can't prove that no out of bounds will happen here as well.
            let fill_buffer = unsafe { buf.get_unchecked_mut(from_raw..from_raw + to_fill_raw) };
            for w in &mut self.wave_ins {
                w.fill_buf::<A, MONO>(fill_buffer, &self.asset);
            }
            for w in &mut self.drum_ins {
                w.fill_buf::<A, MONO>(fill_buffer, &self.asset);
            }
            filled_raw += to_fill_raw;
            // Same thing probably applies here
            if MONO {
                self.remaining_samples -= (to_fill_raw) as f32;
            } else {
                self.remaining_samples -= (to_fill_raw / 2) as f32;
            }
        }
        // Multiplying MASTER_VOLUME in fill_buf is somewhat faster
        // buf.iter_mut().for_each(|f| *f *= MASTER_VOLUME);
    }

    /// Returns (Loop Start, Loop End).
    pub fn get_loop(&self) -> (u32, u32) {
        (self.loop_start, self.loop_end)
    }

    /// Returns current beat.
    pub fn get_beat(&self) -> u32 {
        self.cur_beat
    }

    // TODO: Play till function
    // TODO: Seek function (Will be expensive)
}

/// Builder for [`OrgPlay`].
pub struct OrgPlayBuilder<I, A>(PhantomData<I>, A, u32);

impl OrgPlayBuilder<(), ()> {
    /// Creates new OrgPlayBuilder.
    /// Initial default is [`Linear`](crate::interp_impls::Linear) interpolation and sample rate of 48000Hz.
    ///
    /// Provide Cave Story wavetables and drums
    /// by [`with_asset`](Self::with_asset), or [`with_asset_provider`](Self::with_asset_provider).
    ///
    /// Otherwise it is compile error to call [`build`](Self::build).
    pub fn new() -> OrgPlayBuilder<crate::interp_impls::Linear, ()> {
        OrgPlayBuilder(PhantomData, (), 48000)
    }
}

impl<I, A> OrgPlayBuilder<I, A> {
    pub fn with_interpolation<I2: OrgInterpolation>(self, _: I2) -> OrgPlayBuilder<I2, A> {
        OrgPlayBuilder(PhantomData, self.1, self.2)
    }

    /// # Panics
    ///
    /// Panics if `rate` is less than 1000.
    pub fn with_sample_rate(self, rate: u32) -> OrgPlayBuilder<I, A> {
        assert!(rate >= 1000);
        OrgPlayBuilder(self.0, self.1, rate)
    }

    pub fn with_asset_provider<A2: CaveStoryAssetProvider>(self, a: A2) -> OrgPlayBuilder<I, A2> {
        OrgPlayBuilder(PhantomData, a, self.2)
    }

    pub fn with_asset<'a>(
        self,
        wavetable: &'a [u8; 25600],
        drum: &'a [u8; 40000],
    ) -> OrgPlayBuilder<I, AssetByRef<'a>> {
        self.with_asset_provider(AssetByRef(wavetable, drum))
    }
}

impl<I, A> OrgPlayBuilder<I, A>
where
    I: OrgInterpolation,
    A: CaveStoryAssetProvider,
{
    /// Returns None if song is invalid.
    pub fn build<'a>(self, song: &'a [u8]) -> Option<OrgPlay<'a, I, A>> {
        OrgPlay::<I, A>::new(self.1, song, self.2)
    }
}
