use std::{hint::black_box, time::Instant};

use orgorg::{CaveStoryAssetProvider, OrgPlayBuilder, interp_impls::Linear, wt};

const fn to_wt_array<const N: usize>(arr: [u8; N]) -> [wt; N] {
    let mut a = [unsafe { core::mem::zeroed() }; N];
    let mut i = 0;
    while i < N {
        a[i] = arr[i] as wt;
        i += 1;
    }
    a
}

struct ConstAsset;

impl CaveStoryAssetProvider for ConstAsset {
    #[inline(always)]
    fn wavetable(&self) -> &[wt; 25600] {
        &const { to_wt_array(*include_bytes!("../wavetable.dat")) }
    }

    #[inline(always)]
    fn drum(&self) -> &[wt; 40000] {
        &const { to_wt_array(*include_bytes!("../drums.dat")) }
    }
}

fn main() {
    let song = include_bytes!("../org/Cave Story.org");
    let mut orgplay = OrgPlayBuilder::new()
        .with_sample_rate(black_box(48000))
        .with_interpolation(Linear)
        .with_soundbank_provider(ConstAsset)
        .build(black_box(song))
        .unwrap();
    let mut cur = Instant::now();
    let mut loops = 0;
    let mut buf = vec![0.0; 4096];
    loop {
        orgplay.synth_stereo(&mut buf);
        black_box(&buf);
        loops += 1;
        let elapsed = cur.elapsed().as_secs_f64();
        if elapsed >= 1.0 {
            let bytes = loops * buf.len() * 4;
            println!("{} MB/s", bytes / 1024 / 1024);
            loops = 0;
            cur = Instant::now();
        }
    }
}
