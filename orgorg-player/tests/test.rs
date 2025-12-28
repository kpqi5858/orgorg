use core::f32;

use orgorg::{
    CaveStoryAssetProvider, OrgPlayBuilder,
    interp_impls::{Linear, NoInterp},
};

struct DummyProvider;

const fn generate_dummy_array<const N: usize>() -> [u8; N] {
    let mut ret = [0; N];
    let mut idx = 0;
    while idx < N {
        ret[idx] = idx as u8;
        idx += 1;
    }
    ret
}

impl CaveStoryAssetProvider for DummyProvider {
    fn wavetable(&self) -> &[u8; 25600] {
        &const { generate_dummy_array() }
    }
    fn drum(&self) -> &[u8; 40000] {
        &const { generate_dummy_array() }
    }
}

#[test]
fn empty() {
    let song = include_bytes!("./empty.org");
    let mut player = OrgPlayBuilder::new()
        .with_sample_rate(1000)
        .with_interpolation(Linear)
        .with_asset_provider(DummyProvider)
        .build(song)
        .unwrap();
    let mut buf = vec![f32::NAN; 1024];
    player.synth_mono(&mut buf);
    assert!(buf.iter().all(|v| *v == 0.0));
    let mut buf = vec![f32::NAN; 1024];
    player.synth_stereo(&mut buf);
    assert!(buf.iter().all(|v| *v == 0.0));
}

#[test]
fn extreme_value() {
    let mut song = *include_bytes!("./test1.org");
    // Set ms_per_beat to 65536
    song[6] = 0xff;
    song[7] = 0xff;
    let mut player = OrgPlayBuilder::new()
        .with_sample_rate(u32::MAX)
        .with_interpolation(NoInterp)
        .with_asset_provider(DummyProvider)
        .build(&song)
        .unwrap();
    let mut buf = vec![0.0; 4096];
    player.synth_stereo(&mut buf);
    // Set ms_per_beat to 1
    song[6] = 0x01;
    song[7] = 0x00;
    let mut player = OrgPlayBuilder::new()
        .with_sample_rate(1001)
        .with_interpolation(NoInterp)
        .with_asset_provider(DummyProvider)
        .build(&song)
        .unwrap();
    player.synth_stereo(&mut buf);
}

#[test]
fn test1() {
    let sample_rate: u32 = 1000;
    let seconds = 20;
    let buf_len = sample_rate as usize * seconds;
    let song = include_bytes!("./test1.org");

    // Stereo synthesis
    let mut player = OrgPlayBuilder::new()
        .with_sample_rate(sample_rate)
        .with_interpolation(Linear)
        .with_asset_provider(DummyProvider)
        .build(song)
        .unwrap();
    let mut buf_stereo = vec![0.0_f32; buf_len * 2];
    player.synth_stereo(&mut buf_stereo);

    // Mono synthesis
    let mut player = OrgPlayBuilder::new()
        .with_sample_rate(sample_rate)
        .with_interpolation(Linear)
        .with_asset_provider(DummyProvider)
        .build(song)
        .unwrap();
    let mut buf_mono = vec![0.0_f32; buf_len];
    player.synth_mono(&mut buf_mono);

    // It is already extremely slow to run on miri.
    // Don't run these logic tests on miri.
    #[cfg(not(miri))]
    {
        assert!(buf_mono.iter().cloned().all(f32::is_finite));
        assert!(buf_stereo.iter().cloned().all(f32::is_finite));
        // Is downmixed stereo sound equal to mono sound?
        for (idx, (a, b)) in buf_stereo
            .chunks_exact(2)
            .map(|a| (a[0] + a[1]) / 2.0)
            .zip(buf_mono.iter().copied())
            .enumerate()
        {
            let diff = (a - b).abs();
            assert!(diff < 1e-6, "Idx {idx} - A: {a}, B: {b}, Diff: {diff}");
        }
        let mut player = OrgPlayBuilder::new()
            .with_sample_rate(sample_rate)
            .with_interpolation(Linear)
            .with_asset_provider(DummyProvider)
            .build(song)
            .unwrap();
        // Is output of synthesis output consistent with buffer size?
        let mut buf_synth_splited = vec![];
        while buf_synth_splited.len() < buf_len {
            let mut buf2 =
                vec![0.0_f32; std::cmp::min(456, buf_mono.len() - buf_synth_splited.len())];
            player.synth_mono(&mut buf2);
            buf_synth_splited.append(&mut buf2);
        }
        assert_eq!(buf_synth_splited, buf_mono);
    }
}
