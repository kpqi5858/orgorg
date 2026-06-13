#![cfg_attr(not(feature = "std"), no_std)]

//! `no_std` compatible Cave Story Organya Music Player.
//!
//! Partially based on bisqwit's C++ OrgPlay.
//!
//! Designed to be 100% pure, side-effect free.
//!
//! # Example
//! ```no_run
//! // Basic example for playing Org-02 music with original Cave Story drum sound effects.
//! use orgorg::{OrgPlay, OrgPlayBuilder, AssetByRef, interp_impls::Linear};
//!
//! let wavetable: &[i8; 25600] = todo!();
//! let drum: &[i8; 40000] = todo!();
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
//!     // Process buffer and output
//! }
//! ```
//!
//! For owned [`OrgPlay`], use self-referential struct helpers like
//! [`self_cell`](https://crates.io/crates/self_cell) or [`ouroboros`](https://crates.io/crates/ouroboros).
//! See orgorg-player for example.
//!
//! # How to get data needed for synthesis
//! See [orgorg-player](https://github.com/kpqi5858/orgorg/tree/main/orgorg-player) project.
//! Run `orgorg-player dump` for Cave Story wavetable and drums.
//!
//! And see [`wdb`](https://github.com/kpqi5858/orgorg/blob/main/orgorg-player/src/wdb.rs)
//! module in orgorg-player for loading `soundbank.wdb`.
//!
//! # Cargo Features: `simd`
//!
//! Uses [`wide`](https://crates.io/crates/wide) crate for synthesis with 8-lane SIMD,
//! which may gain performance where the platform can benefit from it.
//!
//! On my x86 PC with AVX2 and Raspberry Pi 5, it yields up to ~2x speedup.
//!
//! Keep in mind that:
//! - There is no built-in multiversioning.
//! - If the platform or build configuration does not support SIMD well,
//!   it can result in worse performance due to scalar emulation of SIMD instructions.
//! - The output may differ slightly between `simd` and non-`simd`.
//! - API is incompatible between `simd` and non-`simd`.
//!   - Type of drums and wavetable becomes f32 instead of i8, for performance reasons.
//!   - [`OrgInterpolation`] functions are mutually exclusive.
//!
//! # Performance
//! It is fast and does not allocate memory at all. But with following caveats.
//!
//! - FPU should be present for maximum performance,
//!   since there are lots of single-precision(f32) floating point arithmetic.
//! - This crate uses some unsafe to boost the performance.
//!   The author tried to ensure safety but, who knows. Feel free to audit the code.
//! - As you might guessed from generic [`OrgPlay`] type,
//!   constructing many variants of `OrgPlay` may lead to size bloat.

use core::{cmp, marker::PhantomData, mem::MaybeUninit, num::Wrapping, ptr::NonNull};

const MASTER_VOLUME: f32 = 1.0 / (1 << 19) as f32;

/// Type of drums and wavetable data.
///
/// [`f32`] if `simd`, [`i8`] if not `simd`.
pub type OrgSmp = f32;

/// Provides original Cave Story wavetable and drum samples to [`OrgPlay`].
///
/// With this trait, it can play Org-02 musics that uses original Cave Story drum sound effects.
/// In other words, drum channel only plays wave 0, 2, 4, 5, 6, 8.
///
/// You don't need to implement this trait to use [`OrgPlay`],
/// as [`OrgPlayBuilder::with_asset`] will use default implementation
/// that holds references to the data.
pub trait CaveStoryAssetProvider {
    /// The original `wavetable.dat` file.
    fn wavetable(&self) -> &[OrgSmp; 25600];
    /// 6 pxt samples concatenated.
    ///
    /// Order is: fx96, fx97, fx9a, fx98, fx99, fx9b
    fn drum(&self) -> &[OrgSmp; 40000];
}

/// Provides wavetable and drum samples to [`OrgPlay`].
///
/// You don't really need to implement this trait yourself,
/// as [`Soundbank`] and [`CaveStoryAssetProvider`] provides implementation for this trait.
///
/// # Safety
/// - Return value of [`SoundbankProvider::is_drum_valid`]
///   must be consistent for given `idx` across all calls.
/// - If [`SoundbankProvider::is_drum_valid`] returns `true` for given `idx`,
///   [`SoundbankProvider::get_drum`] must return a slice with `[1, 500000]` length,
///   and its length must be consistent across all calls.
///
/// In other words, don't tamper with outputs using interior mutability or external source.
pub unsafe trait SoundbankProvider {
    /// The original `wavetable.dat` file, or 100 concatenated 256-length waves.
    fn wavetable(&self) -> &[OrgSmp; 25600];

    /// The drum channel with `idx` wave will be silenced if this returns `false`.
    fn is_drum_valid(&self, idx: u8) -> bool;

    /// Get drum sample of `idx`.
    /// # Safety
    /// Caller must not call this function
    /// if [`SoundbankProvider::is_drum_valid`] with given `idx` would return `false`.
    unsafe fn get_drum(&self, idx: u8) -> &[OrgSmp];
}

// Safety: All function is consistent.
unsafe impl<T: CaveStoryAssetProvider> SoundbankProvider for T {
    #[inline(always)]
    fn wavetable(&self) -> &[OrgSmp; 25600] {
        CaveStoryAssetProvider::wavetable(self)
    }

    #[inline(always)]
    fn is_drum_valid(&self, idx: u8) -> bool {
        matches!(idx, 0 | 2 | 4 | 5 | 6 | 8)
    }

    #[inline(always)]
    unsafe fn get_drum(&self, idx: u8) -> &[OrgSmp] {
        let drums = CaveStoryAssetProvider::drum(self).as_ptr();
        unsafe {
            let range = match idx {
                0 => (0, 5000),
                2 => (5000, 10000),
                4 => (15000, 10000),
                5 => (25000, 1000),
                6 => (26000, 10000),
                8 => (36000, 4000),
                _ => core::hint::unreachable_unchecked(),
            };
            core::slice::from_raw_parts(drums.add(range.0), range.1)
        }
    }
}

/// Default provider used in [`OrgPlayBuilder::with_asset`]
pub struct AssetByRef<'a>(&'a [OrgSmp; 25600], &'a [OrgSmp; 40000]);

impl CaveStoryAssetProvider for AssetByRef<'_> {
    #[inline(always)]
    fn wavetable(&self) -> &[OrgSmp; 25600] {
        self.0
    }

    #[inline(always)]
    fn drum(&self) -> &[OrgSmp; 40000] {
        self.1
    }
}

/// Custom soundbank by ref.
///
/// 43 drums will play Org-03 songs properly.
#[derive(Clone)]
pub struct Soundbank<'a> {
    wavetable: &'a [OrgSmp; 25600],
    drums: &'a [&'a [OrgSmp]],
}

impl<'a> Soundbank<'a> {
    /// Creates new Soundbank.
    ///
    /// - More than 255 `drums` is effectively ignored.
    /// - If length of a drum is not in `[1, 500000]`,
    ///   that particular drum is considered invalid and won't play a sound.
    pub fn new(wavetable: &'a [OrgSmp; 25600], drums: &'a [&'a [OrgSmp]]) -> Self {
        Self { wavetable, drums }
    }
}

// Safety: All function is consistent.
unsafe impl SoundbankProvider for Soundbank<'_> {
    #[inline(always)]
    fn wavetable(&self) -> &[OrgSmp; 25600] {
        self.wavetable
    }

    #[inline(always)]
    fn is_drum_valid(&self, idx: u8) -> bool {
        let len = self.drums.get(idx as usize).map(|x| x.len()).unwrap_or(0);
        (1..=500000).contains(&len)
    }

    #[inline(always)]
    unsafe fn get_drum(&self, idx: u8) -> &[OrgSmp] {
        unsafe { self.drums.get_unchecked(idx as usize) }
    }
}

/// Interpolation for Organya Music synthesis.
///
/// Keep in mind that these functions are called at audio rate.
/// You would like to put `#[inline]` and optimize them really well.
///
/// Implementer of `OrgInterpolation` must be ZST. Otherwise you will get compilation error.
/// It is meant to be stateless.
pub trait OrgInterpolation {
    /// How many samples prior to `pos` required by the interpolation.
    ///
    /// If the interpolation samples at `pos - N`,
    /// this should be set to `N` to ensure potential trailing non-zero values get written.
    ///
    /// Only relevant for drum.
    const INTERP_REMNANT: u32 = 0;

    /// Interpolate the `wave` from `(pos).(frac)`.
    ///
    /// `pos` should be wrapped by 256 (`& 0xff`) before indexing.
    fn wave(wave: &[f32; 256], pos: u32, frac: f32) -> f32;

    /// Interpolate the `drum` from `(pos).(frac)`.
    ///
    /// Out of bounds `drum` read should be 0.
    ///
    /// If `drum.len()` is too big (Exact value is not specified, but not greater than
    /// [`SoundbankProvider::get_drum`] requirement), it can produce incorrect result.
    fn drum(drum: &[f32], pos: u32, frac: f32) -> f32;
}

/// Builtin [`OrgInterpolation`] implementations.
pub mod interp_impls {
    /// Linear Interpolation. Fast.
    pub struct Linear;

    /// No Interpolation. Fastest.
    pub struct NoInterp;

    /// Lagrange Interpolation. Slow.
    pub struct Lagrange;
}

mod _interp_impls {
    use super::OrgInterpolation;
    use super::interp_impls::*;

    trait BranchlessGather {
        fn get_or_zero(&self, idx: u32) -> f32;
    }

    impl BranchlessGather for [f32] {
        fn get_or_zero(&self, idx: u32) -> f32 {
            let len = self.len() as u32 - 1;
            let cond = 0_u32.wrapping_sub((idx <= len) as u32);
            let actual_idx = idx.min(len);
            let value = unsafe { *self.get_unchecked(actual_idx as usize) };
            f32::from_bits(value.to_bits() & cond)
        }
    }

    impl OrgInterpolation for Linear {
        #[inline(always)]
        fn wave(wave: &[f32; 256], pos: u32, frac: f32) -> f32 {
            let idx1 = pos & 0xff;
            let sample1 = wave[idx1 as usize];
            let idx2 = pos.wrapping_add(1) & 0xff;
            let sample2 = wave[idx2 as usize];
            // The "imprecise" lerp (see Wikipedia Linear Interpolation).
            // Monotonic, and slightly fast over "precise" one.
            (sample2 - sample1).mul_add(frac, sample1)
        }

        #[inline(always)]
        fn drum(drum: &[f32], pos: u32, frac: f32) -> f32 {
            let sample1 = drum.get_or_zero(pos);
            let sample2 = drum.get_or_zero(pos.wrapping_add(1));
            (sample2 - sample1).mul_add(frac, sample1)
        }
    }

    impl OrgInterpolation for NoInterp {
        #[inline(always)]
        fn wave(wave: &[f32; 256], pos: u32, _frac: f32) -> f32 {
            wave[(pos & 0xff) as usize]
        }

        #[inline(always)]
        fn drum(drum: &[f32], pos: u32, _frac: f32) -> f32 {
            drum.get_or_zero(pos)
        }
    }

    impl OrgInterpolation for Lagrange {
        const INTERP_REMNANT: u32 = 1;

        #[inline(always)]
        fn wave(wave: &[f32; 256], pos: u32, frac: f32) -> f32 {
            #[rustfmt::skip]
            let idx = [
                pos.wrapping_sub(1) as usize & 0xff,
                pos                 as usize & 0xff,
                pos.wrapping_add(1) as usize & 0xff,
                pos.wrapping_add(2) as usize & 0xff,
            ];
            let s1 = wave[idx[0]];
            let s2 = wave[idx[1]];
            let s3 = wave[idx[2]];
            let s4 = wave[idx[3]];

            let c0 = s2;
            let c1 = s3 - s1 * (1.0 / 3.0) - s2 * (1.0 / 2.0) - s4 * (1.0 / 6.0);
            let c2 = (s1 + s3) * (1.0 / 2.0) - s2;
            let c3 = (s4 - s1) * (1.0 / 6.0) + (s2 - s3) * (1.0 / 2.0);

            ((c3 * frac + c2) * frac + c1) * frac + c0
        }

        #[inline(always)]
        fn drum(drum: &[f32], pos: u32, frac: f32) -> f32 {
            #[rustfmt::skip]
            let idx = [
                pos.wrapping_sub(1),
                pos               ,
                pos.wrapping_add(1),
                pos.wrapping_add(2),
            ];
            let s1 = drum.get_or_zero(idx[0]);
            let s2 = drum.get_or_zero(idx[1]);
            let s3 = drum.get_or_zero(idx[2]);
            let s4 = drum.get_or_zero(idx[3]);

            let c0 = s2;
            let c1 = s3 - s1 * (1.0 / 3.0) - s2 * (1.0 / 2.0) - s4 * (1.0 / 6.0);
            let c2 = (s1 + s3) * (1.0 / 2.0) - s2;
            let c3 = (s4 - s1) * (1.0 / 6.0) + (s2 - s3) * (1.0 / 2.0);

            ((c3 * frac + c2) * frac + c1) * frac + c0
        }
    }
}

struct Event {
    note: u8,
    length: u8,
    volume: u8,
    panning: u8,
}

struct Instrument<const DRUM: bool> {
    tuning: u16,
    pi: bool,
    // Supposedly the maximum number of events in a single instrument is 256.
    // Some incompatible(non-standard?) music can exceed that arbitrary limit.
    // So, be lenient here.
    n_events: u16,
    cur_event: u16,
    // TODO: Pre-calculate this value, not on the fly
    loop_event: Option<u16>,
    phase_inc: u32,
    phase_acc: u32,
    cur_pan: u8,
    cur_vol: u8,
    // Invariants:
    // - If n_events != 0, must point to valid wave
    wave_idx: u8,
    cur_len_or_phase_acc: u32,
}

unsafe impl<const DRUM: bool> Send for Instrument<DRUM> {}
unsafe impl<const DRUM: bool> Sync for Instrument<DRUM> {}

// 8.24 fixed point arithmetic
pub const I24: u32 = 0x1000000;
pub const I24MASK: u32 = I24 - 1;
pub const F24: f32 = I24 as f32;

impl<const DRUM: bool> Instrument<DRUM> {
    // Safety: cur_event < n_events
    unsafe fn get_cur_event_beat(&self, ptr: NonNull<u8>) -> u32 {
        debug_assert!(self.cur_event < self.n_events);
        // Safety: See inst_data_ptr field comment
        unsafe { ptr.add(self.cur_event as usize * 4).cast().read_unaligned() }
    }

    // Safety: cur_event < n_events
    unsafe fn get_cur_event(&self, ptr: NonNull<u8>) -> Event {
        debug_assert!(self.cur_event < self.n_events);
        // Safety: See inst_data_ptr field comment
        unsafe {
            let n_events = self.n_events as usize;
            let inst_ptr = ptr.add(n_events * 4 + self.cur_event as usize);
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

    fn tick(&mut self, cur_beat: u32, loop_start: u32, rate: u32, ptr: NonNull<u8>) {
        // There is no official documentation for .org file,
        // and these logics are not designed to handle it as leniently as possible.
        // It assumes that event is sorted by its beat, and no more event after loop_end.
        // But OrgMaker (the only official .org editor) output follows those rule.
        //
        // Unofficial reference
        // https://gist.github.com/fdeitylink/7fc9ddcc54b33971e5f505c8da2cfd28
        if cur_beat == loop_start {
            if let Some(loop_event) = self.loop_event {
                self.cur_event = loop_event;
            } else {
                self.loop_event = Some(self.cur_event);
            }
        }
        if !DRUM && !self.pi {
            self.cur_len_or_phase_acc = self.cur_len_or_phase_acc.saturating_sub(1);
        }
        if self.cur_event >= self.n_events {
            return;
        }
        // Safety: Checked with above code
        let event = unsafe {
            let cur_event_beat = self.get_cur_event_beat(ptr);
            if cur_event_beat == cur_beat {
                self.get_cur_event(ptr)
            } else {
                return;
            }
        };
        self.cur_event += 1;
        if event.volume != 255 {
            self.cur_vol = event.volume;
        }
        if event.panning != 255 {
            const fn p(p: u8) -> u8 {
                const fn min(a: u8, b: u8) -> u8 {
                    if a > b { b } else { a }
                }
                let left = min(6, 12 - p);
                let right = min(6, p);
                (left << 4) | right
            }
            #[rustfmt::skip]
            const LUT: [u8; 13] = [ p(0), p(1), p(2), p(3), p(4), p(5), p(6), p(7), p(8), p(9), p(10), p(11), p(12) ];
            self.cur_pan = LUT[event.panning.min(12) as usize];
        }
        if event.note != 255 {
            self.cur_len_or_phase_acc = 0;
            self.phase_acc = 0;
            fn calc_inc(freq: u32, rate: u32) -> Option<u32> {
                let res = (freq as i32 as f32) / (rate as i32 as f32);
                if res >= 256.0 {
                    None
                } else {
                    unsafe {
                        let i = res.to_int_unchecked::<i32>() as u32;
                        let sub = res - i as f32;
                        Some((i << 24) | (sub * F24).to_int_unchecked::<i32>() as u32)
                    }
                }
            }
            if DRUM {
                let freq = event.note as u32 * 800 + 100;
                if let Some(inc) = calc_inc(freq, rate) {
                    self.phase_inc = inc;
                }
            } else {
                const FRQ_TABLE: [u32; 12] =
                    [262, 277, 294, 311, 330, 349, 370, 392, 415, 440, 466, 494];
                let freq = FRQ_TABLE[(event.note % 12) as usize];
                let oct = 1 << (5 + (event.note / 12).min(7) as i32);
                let final_freq = (freq * oct) + (self.tuning as u32 - 1000);
                let phase_inc = calc_inc(final_freq, rate);
                if let Some(inc) = phase_inc {
                    self.phase_inc = inc;
                    self.cur_len_or_phase_acc = if self.pi {
                        // TODO: I dont know what is the accurate formula for pi instrument
                        (oct + 1) * 4 * 256
                    } else {
                        event.length as u32
                    };
                }
            }
        }
    }

    // This function is the critical part of overall performance.
    fn fill_buf<A: SoundbankProvider, I: OrgInterpolation, const MONO: bool>(
        &mut self,
        buf: &mut [f32],
        a: &A,
    ) {
        if !DRUM && self.cur_len_or_phase_acc == 0 {
            return;
        }
        if DRUM && self.phase_inc == 0 {
            return;
        }
        // Safety: See wave_idx field comment
        let cur_wave = unsafe {
            if DRUM {
                debug_assert!(a.is_drum_valid(self.wave_idx));
                a.get_drum(self.wave_idx)
            } else {
                debug_assert!((0..100).contains(&self.wave_idx));
                let idx = self.wave_idx as usize * 256;
                let w = a.wavetable().as_ptr();
                core::slice::from_raw_parts(w.add(idx), 256)
            }
        };
        let vol = self.cur_vol as i32;
        // Integer multiplication then float cast is slightly faster
        let left = ((self.cur_pan >> 4) as i32 * vol) as f32 * MASTER_VOLUME;
        let right = ((self.cur_pan & 0b00001111) as i32 * vol) as f32 * MASTER_VOLUME;
        let mono = (((self.cur_pan >> 4) + (self.cur_pan & 0b00001111)) as i32 * vol) as f32
            * (MASTER_VOLUME / 2.0);

        let n = match (MONO, self.pi) {
            (true, false) => buf.len(),
            (false, false) => buf.len() / 2,
            (true, true) => cmp::min(buf.len(), self.cur_len_or_phase_acc as usize),
            (false, true) => cmp::min(buf.len() / 2, self.cur_len_or_phase_acc as usize),
        };
        let buf = unsafe {
            let n_len = if MONO { n } else { n * 2 };
            buf.get_unchecked_mut(0..n_len)
        };

        let inc_i = self.cur_len_or_phase_acc >> 24;
        let wave_inc = self.phase_inc;
        let inc_sub_24 = self.phase_inc & I24MASK;

        let mut pos = Wrapping(self.phase_acc);
        let mut pos_sub = self.cur_len_or_phase_acc;

        for chunk in buf.chunks_mut(if MONO { 256 } else { 512 }) {
            for chunk in chunk.chunks_exact_mut(if MONO { 1 } else { 2 }) {
                let sample = unsafe {
                    if DRUM {
                        let base_pos = pos.0 + (pos_sub >> 24);
                        core::hint::assert_unchecked(base_pos < 500000 + 256 * 256 + 256);
                        core::hint::assert_unchecked((1..=500000).contains(&cur_wave.len()));
                        let frac = (pos_sub & I24MASK) as f32 / F24;
                        let val = I::drum(cur_wave, base_pos, frac);
                        pos_sub += inc_sub_24;
                        pos += inc_i;
                        val
                    } else {
                        let base_pos = pos.0 >> 24;
                        let frac = ((pos.0 & I24MASK) as f32) / F24;
                        let val = I::wave(cur_wave.try_into().unwrap(), base_pos, frac);
                        pos += wave_inc;
                        val
                    }
                };
                if MONO {
                    let v = &mut chunk[0];
                    *v = sample.mul_add(mono, *v);
                } else {
                    let v = &mut chunk[0];
                    *v = sample.mul_add(left, *v);
                    let v = &mut chunk[1];
                    *v = sample.mul_add(right, *v);
                }
            }
            if DRUM {
                pos += pos_sub >> 24;
                pos_sub &= I24MASK;
                if pos.0 >= cur_wave.len() as u32 + I::INTERP_REMNANT {
                    self.phase_inc = 0;
                    return;
                }
            }
        }

        self.phase_acc = pos.0;
        self.cur_len_or_phase_acc = pos_sub;
        if !DRUM && self.pi {
            self.cur_len_or_phase_acc -= n as u32;
        }
    }
}

/// Playback option for [`OrgPlay`].
#[derive(Default, Clone, Copy)]
pub enum PlayTill {
    /// Play endlessly.
    #[default]
    Endless,
    /// Play until specified beat.
    ///
    /// If the specified beat is out of range for the song, it will behave like `Endless`.
    Beat(u32),
    /// Play until song loops.
    Loop,
}

/// Result of [`OrgPlay`] playback, according to [`PlayTill`] option.
pub struct PlayResult(bool, usize);

impl PlayResult {
    /// Returns `true` if the playback have reached the end.
    pub fn reached_end(&self) -> bool {
        self.0
    }

    /// If the playback have reached the end, length of filled samples in the buffer.
    /// Rest of the buffer is filled with `0.0`.
    ///
    /// Else, this is always the full length of the buffer.
    pub fn filled_length(&self) -> usize {
        self.1
    }
}

/// `no_std` compatible Cave Story Organya Music Player.
pub struct OrgPlay<'a, I: OrgInterpolation, A: SoundbankProvider> {
    song_data: NonNull<u8>,
    _song_data_ref: PhantomData<&'a [u8]>,
    sample_rate: u32,
    samples_per_beat: i32,
    remaining_samples: i32,
    loop_start: u32,
    loop_end: u32,
    cur_beat: u32,
    wave_ins: [Instrument<false>; 8],
    drum_ins: [Instrument<true>; 8],
    asset: A,
    _i: PhantomData<I>,
}

unsafe impl<'a, I: OrgInterpolation, A: SoundbankProvider + Send> Send for OrgPlay<'a, I, A> {}
unsafe impl<'a, I: OrgInterpolation, A: SoundbankProvider + Sync> Sync for OrgPlay<'a, I, A> {}

impl<'a, I: OrgInterpolation, A: SoundbankProvider> OrgPlay<'a, I, A> {
    fn new(asset: A, song: &'a [u8], rate: u32) -> Option<Self> {
        struct UnsafeReader<'a>(&'a [u8]);
        impl<'a> UnsafeReader<'a> {
            unsafe fn new(a: &'a [u8]) -> Self {
                Self(a)
            }

            fn read<const N: usize>(&self, offset: usize) -> [u8; N] {
                unsafe { self.0.get_unchecked(offset..offset + N).try_into().unwrap() }
            }

            fn read_u8(&self, offset: usize) -> u8 {
                self.read::<1>(offset)[0]
            }

            fn read_u16(&self, offset: usize) -> u16 {
                u16::from_le_bytes(self.read(offset))
            }

            fn read_u32(&self, offset: usize) -> u32 {
                u32::from_le_bytes(self.read(offset))
            }
        }

        if song.len() < 114 {
            return None;
        }
        // Safety: all following read is within index < 114
        let song_reader = unsafe { UnsafeReader::new(song) };
        if !matches!(&song[0..6], b"Org-02" | b"Org-03") {
            return None;
        }
        let ms_per_beat = song_reader.read_u16(6);
        if ms_per_beat == 0 {
            return None;
        }
        let samples_per_beat: i32 = rate.checked_mul(ms_per_beat as u32)?.try_into().ok()?;
        // To prevent overflow in synth method
        if samples_per_beat > i32::MAX / 1000 * 1000 {
            return None;
        }
        let loop_start = song_reader.read_u32(10);
        let loop_end = song_reader.read_u32(14);
        if loop_end < loop_start {
            return None;
        }

        let mut offset = 18;
        let mut ins_data_offset = 114;

        // core::array really needs try_from_fn, or array::try_map
        // Instrument does not allocate anything so no risk of memory leak when early returns.
        let mut wave_ins = [const { MaybeUninit::uninit() }; 8];
        let mut drum_ins = [const { MaybeUninit::uninit() }; 8];

        for val in &mut wave_ins {
            let wave = song_reader.read_u8(offset + 2);
            let valid_wave = (0..100).contains(&wave);
            let n_events = song_reader.read_u16(offset + 4);
            let pi = song_reader.read_u8(offset + 3) != 0;
            let inst_data_ptr = if n_events == 0 {
                NonNull::dangling()
            } else {
                let inst_data =
                    song.get(ins_data_offset..ins_data_offset + n_events as usize * 8)?;
                // Safety: slice is always valid, and bound checked
                unsafe { NonNull::new_unchecked(inst_data.as_ptr() as *mut u8) }
            };
            let mut ret = Instrument {
                tuning: song_reader.read_u16(offset),
                pi,
                n_events: if valid_wave { n_events } else { 0 }, // Must be 0 for invalid wave
                phase_inc: 0,
                phase_acc: 0,
                cur_pan: 0,
                cur_vol: 0,
                cur_len_or_phase_acc: 0,
                cur_event: 0,
                loop_event: None,
                wave_idx: wave,
            };
            // Initial ticking for beat 0, since synth function will start ticking at beat 1
            ret.tick(0, loop_start, rate, inst_data_ptr);
            offset += 6;
            ins_data_offset += n_events as usize * 8;
            val.write(ret);
        }
        for val in &mut drum_ins {
            let wave = song_reader.read_u8(offset + 2);
            let valid_wave = asset.is_drum_valid(wave);
            let n_events = song_reader.read_u16(offset + 4);
            let pi = song_reader.read_u8(offset + 3) != 0;
            let inst_data_ptr = if n_events == 0 {
                NonNull::dangling()
            } else {
                let inst_data =
                    song.get(ins_data_offset..ins_data_offset + n_events as usize * 8)?;
                // Safety: slice is always valid, and bound checked
                unsafe { NonNull::new_unchecked(inst_data.as_ptr() as *mut u8) }
            };
            let mut ret = Instrument {
                tuning: song_reader.read_u16(offset),
                pi,
                n_events: if valid_wave { n_events } else { 0 }, // Must be 0 for invalid wave
                phase_inc: 0,
                phase_acc: 0,
                cur_pan: 0,
                cur_vol: 0,
                cur_len_or_phase_acc: 0,
                cur_event: 0,
                loop_event: None,
                wave_idx: wave,
            };
            // Initial ticking for beat 0, since synth function will start ticking at beat 1
            ret.tick(0, loop_start, rate, inst_data_ptr);
            offset += 6;
            ins_data_offset += n_events as usize * 8;
            val.write(ret);
        }

        // More data after song? Reject.
        if ins_data_offset != song.len() {
            return None;
        }

        let song_data = unsafe { NonNull::new_unchecked(song.as_ptr() as *mut u8).add(114) };

        Some(Self {
            song_data,
            sample_rate: rate,
            samples_per_beat,
            remaining_samples: samples_per_beat,
            loop_start,
            loop_end,
            cur_beat: 0,
            // Safety: They are all initialized now.
            // TODO: Switch to array_assume_init when it lands
            wave_ins: unsafe {
                core::mem::transmute::<[MaybeUninit<Instrument<false>>; 8], [Instrument<false>; 8]>(
                    wave_ins,
                )
            },
            drum_ins: unsafe {
                core::mem::transmute::<[MaybeUninit<Instrument<true>>; 8], [Instrument<true>; 8]>(
                    drum_ins,
                )
            },
            asset,
            _song_data_ref: PhantomData,
            _i: PhantomData,
        })
    }

    /// Advance song and generate 1-channel mono audio data.
    ///
    /// Values can exceed `[-1, 1]` range on some songs.
    pub fn synth_mono(&mut self, buf: &mut [f32]) {
        self.synth_impl::<true>(buf, PlayTill::Endless);
    }

    /// Advance song and generate stereo interleaved audio data.
    ///
    /// Values can exceed `[-1, 1]` range on some songs.
    /// # Panics
    ///
    /// Panics if `buf.len()` is not multiple of 2.
    pub fn synth_stereo(&mut self, buf: &mut [f32]) {
        self.synth_impl::<false>(buf, PlayTill::Endless);
    }

    /// Advance song and generate 1-channel mono audio data, till specified position.
    ///
    /// Values can exceed `[-1, 1]` range on some songs.
    pub fn synth_mono_till(&mut self, buf: &mut [f32], till: PlayTill) -> PlayResult {
        self.synth_impl::<true>(buf, till)
    }

    /// Advance song and generate stereo interleaved audio data, till specified position.
    ///
    /// Values can exceed `[-1, 1]` range on some songs.
    /// # Panics
    ///
    /// Panics if `buf.len()` is not multiple of 2.
    pub fn synth_stereo_till(&mut self, buf: &mut [f32], till: PlayTill) -> PlayResult {
        self.synth_impl::<false>(buf, till)
    }

    fn synth_impl<const MONO: bool>(&mut self, buf: &mut [f32], till: PlayTill) -> PlayResult {
        if !MONO {
            assert!(buf.len().is_multiple_of(2));
        }
        // Just in case if user wants to play till loop_end, which is equivalent to PlayTill::Loop.
        let till = if let PlayTill::Beat(b) = till
            && b == self.loop_end
        {
            PlayTill::Loop
        } else {
            till
        };

        buf.fill(0.0);
        let mut filled_raw = 0;
        while filled_raw < buf.len() {
            if self.remaining_samples <= 0 {
                self.remaining_samples += self.samples_per_beat;
                self.cur_beat += 1;
                let looped;
                if self.cur_beat >= self.loop_end {
                    self.cur_beat = self.loop_start;
                    looped = true;
                } else {
                    looped = false;
                }
                let mut ptr = self.song_data;
                for w in &mut self.wave_ins {
                    w.tick(self.cur_beat, self.loop_start, self.sample_rate, ptr);
                    ptr = unsafe { ptr.add(w.n_events as usize * 8) };
                }
                for w in &mut self.drum_ins {
                    w.tick(self.cur_beat, self.loop_start, self.sample_rate, ptr);
                    ptr = unsafe { ptr.add(w.n_events as usize * 8) };
                }
                match till {
                    PlayTill::Endless => {}
                    PlayTill::Loop => {
                        if looped {
                            return PlayResult(true, filled_raw);
                        }
                    }
                    PlayTill::Beat(b) => {
                        if self.cur_beat == b {
                            return PlayResult(true, filled_raw);
                        }
                    }
                }
            }
            debug_assert!(self.remaining_samples > 0);
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
                    (self.remaining_samples as u32).div_ceil(1000) as usize,
                    buf.len() - filled_raw,
                )
            } else {
                cmp::min(
                    (self.remaining_samples as u32).div_ceil(1000) as usize * 2,
                    buf.len() - filled_raw,
                )
            };
            // Seems compiler can't prove that no out of bounds will happen here as well.
            let fill_buffer = unsafe { buf.get_unchecked_mut(from_raw..from_raw + to_fill_raw) };
            for w in &mut self.wave_ins {
                w.fill_buf::<A, I, MONO>(fill_buffer, &self.asset);
            }
            for w in &mut self.drum_ins {
                w.fill_buf::<A, I, MONO>(fill_buffer, &self.asset);
            }
            filled_raw += to_fill_raw;
            // Same thing probably applies here
            if MONO {
                self.remaining_samples -= to_fill_raw as i32 * 1000;
            } else {
                self.remaining_samples -= to_fill_raw as i32 * 500;
            }
        }
        PlayResult(false, buf.len())
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

    // TODO: Seek function (Will be expensive)
}

/// Builder for [`OrgPlay`].
pub struct OrgPlayBuilder<I, A>(PhantomData<I>, A, u32);

impl OrgPlayBuilder<(), ()> {
    /// Creates new OrgPlayBuilder.
    /// Initial default is [`Linear`](crate::interp_impls::Linear) interpolation and sample rate of 48000Hz.
    ///
    /// Provide soundbank by:
    /// - [`with_soundbank`](Self::with_soundbank)
    /// - [`with_soundbank_provider`](Self::with_soundbank_provider)
    ///
    /// Or, provide original Cave Story wavetable and drums by:
    /// - [`with_asset`](Self::with_asset)
    ///
    /// Otherwise it is compile error to call [`build`](Self::build).
    pub fn new() -> OrgPlayBuilder<crate::interp_impls::Linear, ()> {
        OrgPlayBuilder(PhantomData, (), 48000)
    }
}

impl<I, A> OrgPlayBuilder<I, A> {
    pub fn with_interpolation<I2: OrgInterpolation>(self, _: I2) -> OrgPlayBuilder<I2, A> {
        const {
            assert!(
                core::mem::size_of::<I2>() == 0,
                "Implementer of OrgInterpolation must be ZST"
            );
        }
        OrgPlayBuilder(PhantomData, self.1, self.2)
    }

    /// # Panics
    ///
    /// Panics if `rate` is less than 1000.
    pub fn with_sample_rate(self, rate: u32) -> OrgPlayBuilder<I, A> {
        assert!(rate >= 1000);
        OrgPlayBuilder(self.0, self.1, rate)
    }

    /// Will only properly play songs with original Cave Story drum sound effects.
    /// See [`CaveStoryAssetProvider`] for more information.
    pub fn with_asset<'a>(
        self,
        wavetable: &'a [OrgSmp; 25600],
        drum: &'a [OrgSmp; 40000],
    ) -> OrgPlayBuilder<I, AssetByRef<'a>> {
        self.with_soundbank_provider(AssetByRef(wavetable, drum))
    }

    pub fn with_soundbank(self, a: Soundbank) -> OrgPlayBuilder<I, Soundbank> {
        self.with_soundbank_provider(a)
    }

    pub fn with_soundbank_provider<A2: SoundbankProvider>(self, a: A2) -> OrgPlayBuilder<I, A2> {
        OrgPlayBuilder(PhantomData, a, self.2)
    }
}

impl<I, A> OrgPlayBuilder<I, A>
where
    I: OrgInterpolation,
    A: SoundbankProvider,
{
    /// Returns None if song is invalid.
    pub fn build<'a>(self, song: &'a [u8]) -> Option<OrgPlay<'a, I, A>> {
        OrgPlay::<I, A>::new(self.1, song, self.2)
    }
}
