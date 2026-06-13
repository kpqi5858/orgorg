#![no_std]

//! `no_std` compatible Cave Story Organya Music Player.
//!
//! Partially based on bisqwit's C++ OrgPlay.
//!
//! # Example
//! ```no_run
//! // Basic example for playing Org-02 music with original Cave Story drum sound effects.
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
//! On my x86 PC with AVX2 and Raspberry Pi 5, it yields ~1.8x speedup.
//!
//! Keep in mind that:
//! - There is no built-in multiversioning.
//! - If the platform or build configuration does not support SIMD well,
//!   it can result in worse performance due to scalar emulation of SIMD instructions.
//! - The output may differ slightly between `simd` and non-`simd`.
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

/// Provides original Cave Story wavetable and drum samples to [`OrgPlay`].
///
/// With this trait, it can play Org-02 musics that uses original Cave Story drum sound effects.
/// In other words, drum channel only plays wave 0, 2, 4, 5, 6, 8.
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
    fn wavetable(&self) -> &[u8; 25600];

    /// The drum channel with `idx` wave will be silenced if this returns `false`.
    fn is_drum_valid(&self, idx: u8) -> bool;

    /// Get drum sample of `idx`.
    /// # Safety
    /// Caller must not call this function
    /// if [`SoundbankProvider::is_drum_valid`] with given `idx` would return `false`.
    unsafe fn get_drum(&self, idx: u8) -> &[i8];
}

// Safety: All function is consistent.
unsafe impl<T: CaveStoryAssetProvider> SoundbankProvider for T {
    #[inline(always)]
    fn wavetable(&self) -> &[u8; 25600] {
        CaveStoryAssetProvider::wavetable(self)
    }

    #[inline(always)]
    fn is_drum_valid(&self, idx: u8) -> bool {
        matches!(idx, 0 | 2 | 4 | 5 | 6 | 8)
    }

    #[inline(always)]
    unsafe fn get_drum(&self, idx: u8) -> &[i8] {
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
            core::slice::from_raw_parts(drums.add(range.0).cast(), range.1)
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

/// Custom soundbank by ref.
///
/// 43 drums will play Org-03 songs properly.
#[derive(Clone)]
pub struct Soundbank<'a> {
    wavetable: &'a [u8; 25600],
    drums: &'a [&'a [i8]],
}

impl<'a> Soundbank<'a> {
    /// Creates new Soundbank.
    ///
    /// - More than 255 `drums` is effectively ignored.
    /// - If length of a drum is not in `[1, 500000]`,
    ///   that particular drum is considered invalid and won't play a sound.
    pub fn new(wavetable: &'a [u8; 25600], drums: &'a [&'a [i8]]) -> Self {
        Self { wavetable, drums }
    }
}

// Safety: All function is consistent.
unsafe impl SoundbankProvider for Soundbank<'_> {
    #[inline(always)]
    fn wavetable(&self) -> &[u8; 25600] {
        self.wavetable
    }

    #[inline(always)]
    fn is_drum_valid(&self, idx: u8) -> bool {
        let len = self.drums.get(idx as usize).map(|x| x.len()).unwrap_or(0);
        (1..=500000).contains(&len)
    }

    #[inline(always)]
    unsafe fn get_drum(&self, idx: u8) -> &[i8] {
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
    #[cfg(not(feature = "simd"))]
    fn wave(wave: &[i8; 256], pos: u32, frac: f32) -> f32;

    /// Interpolate the `drum` from `(pos).(frac)`.
    ///
    /// Out of bounds `drum` read should be 0.
    ///
    /// If `drum.len()` is too big (Exact value is not specified, but not greater than
    /// [`SoundbankProvider::get_drum`] requirement), it can produce incorrect result.
    #[cfg(not(feature = "simd"))]
    fn drum(drum: &[i8], pos: u32, frac: f32) -> f32;

    /// Interpolate the `wave` from `(pos).(frac)`, in 8-lane.
    ///
    /// `pos` should be wrapped by 256 (`& 0xff`) before indexing.
    #[cfg(feature = "simd")]
    fn wave_simd(wave: &[i8; 256], pos: wide::u32x8, frac: wide::f32x8) -> wide::f32x8;

    /// Interpolate the `drum` from `(pos).(frac)`, in 8-lane.
    ///
    /// Out of bounds `drum` read should be 0.
    ///
    /// If `drum.len()` is too big (Exact value is not specified, but not greater than
    /// [`SoundbankProvider::get_drum`] requirement), it can produce incorrect result.
    ///
    /// # Safety
    /// `drum` must not be empty slice.
    #[cfg(feature = "simd")]
    unsafe fn drum_simd(drum: &[i8], pos: wide::u32x8, frac: wide::f32x8) -> wide::f32x8;
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

#[cfg(feature = "simd")]
mod _interp_impls {
    use wide::{CmpLe, f32x8, u32x8};

    use super::OrgInterpolation;
    use super::interp_impls::*;

    // Helper functions

    #[inline(always)]
    fn retrieve_wave_data(cur_wave: &[i8; 256], base_pos: u32x8) -> f32x8 {
        unsafe {
            let base_pos = (base_pos & u32x8::splat(0xff)).to_array();
            // If cur_wave were f32 slice, _mm256_i32gather_ps can be used here.
            // This generates 8 read instructions, compared to single VGATHERDPS.
            // But i8 array is friendlier to cpu caches, so I guess cancels out.
            // Also compiler is smart enough to vectorize i8 to f32 cast here.
            f32x8::from(core::array::from_fn(|i| {
                *cur_wave.get_unchecked(base_pos[i] as usize) as f32
            }))
        }
    }

    /// Safety: cur_wave must not be empty
    #[inline(always)]
    unsafe fn retrieve_drum_data(cur_wave: &[i8], base_pos: u32x8) -> f32x8 {
        unsafe {
            let cmp = u32x8::splat(cur_wave.len() as u32 - 1);
            // Casting mask
            let in_bounds: f32x8 = core::mem::transmute(base_pos.simd_le(cmp));
            let base_pos = base_pos.min(cmp).to_array();
            let vals = f32x8::from(core::array::from_fn(|i| {
                *cur_wave.get_unchecked(base_pos[i] as usize) as f32
            }));
            in_bounds.blend(vals, f32x8::splat(0.0))
        }
    }

    impl OrgInterpolation for Linear {
        #[inline(always)]
        fn wave_simd(wave: &[i8; 256], pos: u32x8, frac: f32x8) -> f32x8 {
            let wave_data1 = retrieve_wave_data(wave, pos);
            let wave_data2 = retrieve_wave_data(wave, pos + u32x8::splat(1));
            // Linear Interpolation
            (wave_data2 - wave_data1).mul_add(frac, wave_data1)
        }

        #[inline(always)]
        unsafe fn drum_simd(drum: &[i8], pos: u32x8, frac: f32x8) -> f32x8 {
            unsafe {
                let wave_data1 = retrieve_drum_data(drum, pos);
                let wave_data2 = retrieve_drum_data(drum, pos + u32x8::splat(1));
                // Linear Interpolation
                (wave_data2 - wave_data1).mul_add(frac, wave_data1)
            }
        }
    }

    impl OrgInterpolation for NoInterp {
        #[inline(always)]
        fn wave_simd(wave: &[i8; 256], pos: u32x8, _frac: f32x8) -> f32x8 {
            retrieve_wave_data(wave, pos)
        }

        #[inline(always)]
        unsafe fn drum_simd(drum: &[i8], pos: u32x8, _frac: f32x8) -> f32x8 {
            unsafe { retrieve_drum_data(drum, pos) }
        }
    }

    impl OrgInterpolation for Lagrange {
        const INTERP_REMNANT: u32 = 1;

        #[inline(always)]
        fn wave_simd(wave: &[i8; 256], pos: u32x8, frac: f32x8) -> f32x8 {
            let s1 = retrieve_wave_data(wave, pos - u32x8::splat(1));
            let s2 = retrieve_wave_data(wave, pos);
            let s3 = retrieve_wave_data(wave, pos + u32x8::splat(1));
            let s4 = retrieve_wave_data(wave, pos + u32x8::splat(2));

            let c0 = s2;
            let c1 = s4.mul_add(
                f32x8::splat(-1.0 / 6.0),
                s2.mul_add(
                    f32x8::splat(-1.0 / 2.0),
                    s1.mul_add(f32x8::splat(-1.0 / 3.0), s3),
                ),
            );
            let c2 = (s1 + s3).mul_sub(f32x8::splat(1.0 / 2.0), s2);
            let c3 =
                (s4 - s1).mul_add(f32x8::splat(1.0 / 6.0), (s2 - s3) * f32x8::splat(1.0 / 2.0));

            ((c3.mul_add(frac, c2)).mul_add(frac, c1)).mul_add(frac, c0)
        }

        #[inline(always)]
        unsafe fn drum_simd(drum: &[i8], pos: u32x8, frac: f32x8) -> f32x8 {
            unsafe {
                let s1 = retrieve_drum_data(drum, pos - u32x8::splat(1));
                let s2 = retrieve_drum_data(drum, pos);
                let s3 = retrieve_drum_data(drum, pos + u32x8::splat(1));
                let s4 = retrieve_drum_data(drum, pos + u32x8::splat(2));

                let c0 = s2;
                let c1 = s4.mul_add(
                    f32x8::splat(-1.0 / 6.0),
                    s2.mul_add(
                        f32x8::splat(-1.0 / 2.0),
                        s1.mul_add(f32x8::splat(-1.0 / 3.0), s3),
                    ),
                );
                let c2 = (s1 + s3).mul_sub(f32x8::splat(1.0 / 2.0), s2);
                let c3 =
                    (s4 - s1).mul_add(f32x8::splat(1.0 / 6.0), (s2 - s3) * f32x8::splat(1.0 / 2.0));

                ((c3.mul_add(frac, c2)).mul_add(frac, c1)).mul_add(frac, c0)
            }
        }
    }
}

#[cfg(not(feature = "simd"))]
mod _interp_impls {
    use super::OrgInterpolation;
    use super::interp_impls::*;

    impl OrgInterpolation for Linear {
        #[inline(always)]
        fn wave(wave: &[i8; 256], pos: u32, frac: f32) -> f32 {
            let idx1 = pos & 0xff;
            let sample1 = wave[idx1 as usize];
            let idx2 = pos.wrapping_add(1) & 0xff;
            let sample2 = wave[idx2 as usize];
            // The "imprecise" lerp (see Wikipedia Linear Interpolation).
            // Monotonic, and slightly fast over "precise" one.
            sample1 as f32 + ((sample2 as i32) - (sample1 as i32)) as f32 * frac
        }

        #[inline(always)]
        fn drum(drum: &[i8], pos: u32, frac: f32) -> f32 {
            let sample1 = drum.get(pos as usize).copied().unwrap_or(0);
            let sample2 = drum.get(pos.wrapping_add(1) as usize).copied().unwrap_or(0);
            sample1 as f32 + ((sample2 as i32) - (sample1 as i32)) as f32 * frac
        }
    }

    impl OrgInterpolation for NoInterp {
        #[inline(always)]
        fn wave(wave: &[i8; 256], pos: u32, _frac: f32) -> f32 {
            wave[(pos & 0xff) as usize] as f32
        }

        #[inline(always)]
        fn drum(drum: &[i8], pos: u32, _frac: f32) -> f32 {
            drum.get(pos as usize).copied().unwrap_or(0) as f32
        }
    }

    impl OrgInterpolation for Lagrange {
        const INTERP_REMNANT: u32 = 1;

        #[inline(always)]
        fn wave(wave: &[i8; 256], pos: u32, frac: f32) -> f32 {
            #[rustfmt::skip]
            let idx = [
                pos.wrapping_sub(1) as usize & 0xff,
                pos                 as usize & 0xff,
                pos.wrapping_add(1) as usize & 0xff,
                pos.wrapping_add(2) as usize & 0xff,
            ];
            let s1 = wave[idx[0]] as f32;
            let s2 = wave[idx[1]] as f32;
            let s3 = wave[idx[2]] as f32;
            let s4 = wave[idx[3]] as f32;

            let c0 = s2;
            let c1 = s3 - s1 * (1.0 / 3.0) - s2 * (1.0 / 2.0) - s4 * (1.0 / 6.0);
            let c2 = (s1 + s3) * (1.0 / 2.0) - s2;
            let c3 = (s4 - s1) * (1.0 / 6.0) + (s2 - s3) * (1.0 / 2.0);

            ((c3 * frac + c2) * frac + c1) * frac + c0
        }

        #[inline(always)]
        fn drum(drum: &[i8], pos: u32, frac: f32) -> f32 {
            #[rustfmt::skip]
            let idx = [
                pos.wrapping_sub(1) as usize,
                pos                 as usize,
                pos.wrapping_add(1) as usize,
                pos.wrapping_add(2) as usize,
            ];
            let s1 = drum.get(idx[0]).copied().unwrap_or(0) as f32;
            let s2 = drum.get(idx[1]).copied().unwrap_or(0) as f32;
            let s3 = drum.get(idx[2]).copied().unwrap_or(0) as f32;
            let s4 = drum.get(idx[3]).copied().unwrap_or(0) as f32;

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

struct Instrument<'a, I: OrgInterpolation, const DRUM: bool> {
    // Invariants:
    // - If n_events is 0, this pointer can be dangling so never access it
    // - else, this is a start of &'a [u8] with length of n_events * 8
    // Raw pointer to save a usize space over slice here.
    inst_data_ptr: NonNull<u8>,
    tuning: i16,
    pi: bool,
    // Supposedly the maximum number of events in a single instrument is 256.
    // Some incompatible(non-standard?) music can exceed that arbitrary limit.
    // So, be lenient here.
    n_events: u16,
    cur_event: u16,
    // TODO: Pre-calculate this value, not on the fly
    loop_event: Option<u16>,
    phase_inc: f32,
    phase_acc: u32,
    phase_acc_sub: f32,
    cur_pan: u8,
    cur_vol: u8,
    // Invariants:
    // - If n_events != 0, must point to valid wave
    wave_idx: u8,
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

    fn tick<A: SoundbankProvider>(
        &mut self,
        (cur_beat, loop_start, samples_per_beat, rate, sound): &(u32, u32, f32, u32, &A),
    ) {
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
            self.phase_acc = 0;
            self.phase_acc_sub = 0.0;
            self.cur_len = 0;
            let rate = *rate as f32;
            if DRUM {
                // Safety: See wave_idx field comment
                let wave_len = unsafe { sound.get_drum(self.wave_idx).len() };
                let phase_inc = (event.note as i32 * 800 + 100) as f32 / rate;
                // This is needed for OrgInterpolation trait invariant.
                // And if this condition is false, then the pitch isn't in RATE at all.
                let in_pitch = phase_inc.is_finite() && (0.0..wave_len as f32).contains(&phase_inc);
                if in_pitch {
                    self.phase_inc = phase_inc;
                    // Length logic will be handled in fill_buf
                    self.cur_len = 1;
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
                    self.cur_len = if self.pi {
                        // TODO: I don't know what is the accurate formula for "pi" instrument
                        // But I think this is incorrect
                        (1024.0 / phase_inc) as u32
                    } else {
                        (event.length as f32 * samples_per_beat) as u32
                    };
                }
            }
        }
    }

    // This function is the critical part of overall performance.
    fn fill_buf<A: SoundbankProvider, const MONO: bool>(&mut self, buf: &mut [f32], a: &A) {
        if self.cur_len == 0 {
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
                core::slice::from_raw_parts(w.add(idx).cast(), 256)
            }
        };
        debug_assert!((1..=500000).contains(&cur_wave.len()));
        let vol = self.cur_vol as i32;
        // Integer multiplication then float cast is slightly faster
        let left = ((self.cur_pan >> 4) as i32 * vol) as f32 * MASTER_VOLUME;
        let right = ((self.cur_pan & 0b00001111) as i32 * vol) as f32 * MASTER_VOLUME;
        let mono = (((self.cur_pan >> 4) + (self.cur_pan & 0b00001111)) as i32 * vol) as f32
            * (MASTER_VOLUME / 2.0);
        let n = match (DRUM, MONO) {
            (true, true) => buf.len(),
            (true, false) => buf.len() / 2,
            (false, true) => cmp::min(buf.len(), self.cur_len as usize),
            (false, false) => cmp::min(buf.len() / 2, self.cur_len as usize),
        };
        let inc = self.phase_inc;
        // Safety:
        // There is check in tick() method that ensures 0 <= phase_inc < len.
        let inc_i = unsafe {
            let i = self.phase_inc.to_int_unchecked::<i32>();
            // Saves an instruction needed for sign extension.
            core::hint::assert_unchecked(i >= 0);
            i as u32
        };

        let inc_sub = inc - inc_i as f32;

        let mut pos = Wrapping(self.phase_acc);
        let mut pos_sub = self.phase_acc_sub;

        #[cfg(feature = "simd")]
        {
            use wide::{f32x8, u32x8};

            // Usually remainder seems to be processed in scalar, but it was slower in my benchmark.
            let simd_path_cnt = n.div_ceil(8);
            let simd_path_rem = n % 8;
            unsafe {
                for i in 0..simd_path_cnt {
                    let lane: u32x8 = [0, 1, 2, 3, 4, 5, 6, 7].into();
                    let base_pos = u32x8::splat(pos.0) + lane * u32x8::splat(inc_i);
                    let lane: f32x8 = [0.0, 1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0].into();
                    let sub_pos = lane.mul_add(f32x8::splat(inc_sub), f32x8::splat(pos_sub));
                    // i32 to u32 cast
                    let sub_pos_i: u32x8 = core::mem::transmute(sub_pos.fast_trunc_int());
                    let sub_floor: f32x8 = sub_pos.floor();

                    let base_pos = base_pos + sub_pos_i;
                    let sub_frac = sub_pos - sub_floor;

                    let result = if DRUM {
                        I::drum_simd(cur_wave, base_pos, sub_frac)
                    } else {
                        // Non-DRUM cur_wave is always 256-length.
                        I::wave_simd(cur_wave.try_into().unwrap_unchecked(), base_pos, sub_frac)
                    };

                    if i == simd_path_cnt - 1 && simd_path_rem != 0 {
                        // We calculated excess. Writing them all will cause oob write.
                        for (idx, sample) in result
                            .to_array()
                            .into_iter()
                            .take(simd_path_rem)
                            .enumerate()
                        {
                            // TODO: Would like to use fma here. Wait for float_algebraic.
                            if MONO {
                                *buf.get_unchecked_mut(i * 8 + idx) += sample * mono;
                            } else {
                                *buf.get_unchecked_mut(i * 16 + idx * 2) += sample * left;
                                *buf.get_unchecked_mut(i * 16 + idx * 2 + 1) += sample * right;
                            }
                        }

                        pos_sub = sub_frac.to_array()[simd_path_rem];
                        pos = Wrapping(base_pos.to_array()[simd_path_rem]);
                    } else {
                        // Compiler is able to autovectorize below code nicely,
                        // but obviously does not emit fma.
                        // for (idx, sample) in result.to_array().into_iter().enumerate() {
                        //     if MONO {
                        //         *buf.get_unchecked_mut(i * 8 + idx) += sample * mono;
                        //     } else {
                        //         *buf.get_unchecked_mut(i * 16 + idx * 2) += sample * left;
                        //         *buf.get_unchecked_mut(i * 16 + idx * 2 + 1) += sample * right;
                        //     }
                        // }

                        // TODO: Wait for float_algebraic and rely on compiler, not this ugly code.
                        // Because above code can use AVX512, and use 2 less instructions in arm64.
                        // Still though, this saves 1 or 2 instructions.
                        if MONO {
                            let mono_out = result;
                            let buf_1_ptr = buf.as_mut_ptr().add(i * 8);
                            let buf_1 = buf_1_ptr.cast::<f32x8>().read_unaligned();
                            let buf_1_res = mono_out.mul_add(f32x8::splat(mono), buf_1);
                            buf_1_ptr.cast::<f32x8>().write_unaligned(buf_1_res);
                        } else {
                            let r = result.to_array();
                            // Hopefully compiler optimizes this into vector permutation
                            let stereo_out = (
                                f32x8::from([r[0], r[0], r[1], r[1], r[2], r[2], r[3], r[3]]),
                                f32x8::from([r[4], r[4], r[5], r[5], r[6], r[6], r[7], r[7]]),
                            );
                            let stereo_vol =
                                f32x8::from([left, right, left, right, left, right, left, right]);
                            let buf_1_ptr = buf.as_mut_ptr().add(i * 16);
                            let buf_2_ptr = buf.as_mut_ptr().add(i * 16 + 8);
                            let buf_1 = buf_1_ptr.cast::<f32x8>().read_unaligned();
                            let buf_2 = buf_2_ptr.cast::<f32x8>().read_unaligned();
                            let buf_1_res = stereo_out.0.mul_add(stereo_vol, buf_1);
                            let buf_2_res = stereo_out.1.mul_add(stereo_vol, buf_2);
                            buf_1_ptr.cast::<f32x8>().write_unaligned(buf_1_res);
                            buf_2_ptr.cast::<f32x8>().write_unaligned(buf_2_res);
                        }

                        pos_sub += inc_sub * 8.0;
                        let sub_i = pos_sub.to_int_unchecked::<i32>();
                        pos_sub -= sub_i as f32;
                        pos += inc_i * 8 + sub_i as u32;
                    }

                    if DRUM && pos.0 >= cur_wave.len() as u32 + I::INTERP_REMNANT {
                        self.cur_len = 0;
                        return;
                    }
                }
            }
        }
        #[cfg(not(feature = "simd"))]
        {
            for i in 0..n {
                // Technically failing this assert does not cause UB, but just for correctness.
                debug_assert!((0.0..1.0).contains(&pos_sub));
                let sample = unsafe {
                    if DRUM {
                        I::drum(cur_wave, pos.0, pos_sub)
                    } else {
                        // Non-DRUM cur_wave is always 256-length.
                        I::wave(cur_wave.try_into().unwrap_unchecked(), pos.0, pos_sub)
                    }
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
                pos_sub += inc_sub;
                // We know that pos_sub is in 0..1 range so this is faster than naive integer cast.
                let val = if pos_sub >= 1.0 { 1 } else { 0 };
                pos += val as u32 + inc_i;
                pos_sub -= val as f32;
                if DRUM && pos.0 >= cur_wave.len() as u32 + I::INTERP_REMNANT {
                    self.cur_len = 0;
                    return;
                }
            }
        }

        self.phase_acc = pos.0;
        self.phase_acc_sub = pos_sub;
        if !DRUM {
            self.cur_len -= n as u32;
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
    sample_rate: u32,
    // I want to make this integer, but then RATE must be multiple of 1000.
    samples_per_beat: f32,
    remaining_samples: f32,
    loop_start: u32,
    loop_end: u32,
    cur_beat: u32,
    wave_ins: [Instrument<'a, I, false>; 8],
    drum_ins: [Instrument<'a, I, true>; 8],
    asset: A,
}

impl<'a, I: OrgInterpolation, A: SoundbankProvider> OrgPlay<'a, I, A> {
    fn new(asset: A, song: &'a [u8], rate: u32) -> Option<Self> {
        trait U8SliceExt {
            fn read_i16(&self, offset: usize) -> i16;
            fn read_u16(&self, offset: usize) -> u16;
            fn read_u32(&self, offset: usize) -> u32;
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
        }

        if song.len() < 114 {
            return None;
        }
        if !matches!(&song[0..6], b"Org-02" | b"Org-03") {
            return None;
        }
        let ms_per_beat = song.read_u16(6);
        if ms_per_beat == 0 {
            return None;
        }
        let samples_per_beat = ms_per_beat as f32 * (rate as f32 / 1000.0);
        let loop_start = song.read_u32(10);
        let loop_end = song.read_u32(14);
        if loop_end < loop_start {
            return None;
        }

        let mut offset = 18;
        let mut ins_data_offset = 114;
        let tick_args = &(0, loop_start, samples_per_beat, rate, &asset);

        // core::array really needs try_from_fn, or array::try_map
        // Instrument does not allocate anything so no risk of memory leak when early returns.
        let mut wave_ins = [const { MaybeUninit::uninit() }; 8];
        let mut drum_ins = [const { MaybeUninit::uninit() }; 8];

        for val in &mut wave_ins {
            let wave = song[offset + 2];
            let valid_wave = (0..100).contains(&wave);

            let n_events = song.read_u16(offset + 4);
            let pi = song[offset + 3] != 0;
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
                pi,
                n_events: if valid_wave { n_events } else { 0 }, // Must be 0 for invalid wave
                phase_inc: 0.0,
                phase_acc: 0,
                phase_acc_sub: 0.0,
                cur_pan: 0,
                cur_vol: 0,
                cur_len: 0,
                cur_event: 0,
                loop_event: None,
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
            let wave = song[offset + 2];
            let valid_wave = asset.is_drum_valid(wave);
            let n_events = song.read_u16(offset + 4);
            let pi = song[offset + 3] != 0;
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
                pi,
                n_events: if valid_wave { n_events } else { 0 }, // Must be 0 for invalid wave
                phase_inc: 0.0,
                phase_acc: 0,
                phase_acc_sub: 0.0,
                cur_pan: 0,
                cur_vol: 0,
                cur_len: 0,
                cur_event: 0,
                loop_event: None,
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
            if self.remaining_samples <= 0.0 {
                self.remaining_samples += self.samples_per_beat;
                self.cur_beat += 1;
                let looped;
                if self.cur_beat >= self.loop_end {
                    self.cur_beat = self.loop_start;
                    looped = true;
                } else {
                    looped = false;
                }
                // Since they don't change, making and passing a reference to the tuple is
                // slightly faster than passing individual arguments.
                let tick_args = &(
                    self.cur_beat,
                    self.loop_start,
                    self.samples_per_beat,
                    self.sample_rate,
                    &self.asset,
                );
                for w in &mut self.wave_ins {
                    w.tick(tick_args);
                }
                for w in &mut self.drum_ins {
                    w.tick(tick_args);
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
            debug_assert!(self.remaining_samples > 0.0);
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
                // TODO: Drop libm dependency when core_float_math lands,
                // since this is the only place libm is used,
                // and this will block generating native ceil instruction.
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
        wavetable: &'a [u8; 25600],
        drum: &'a [u8; 40000],
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
