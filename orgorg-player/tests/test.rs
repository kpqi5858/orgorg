use core::f32;

use orgorg::{
    CaveStoryAssetProvider, OrgPlayBuilder,
    interp_impls::{Linear, NoInterp},
};

struct DummyProvider;

impl CaveStoryAssetProvider for DummyProvider {
    fn wavetable(&self) -> &[u8; 25600] {
        &[0xff; 25600]
    }
    fn drum(&self) -> &[u8; 40000] {
        &[0xff; 40000]
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
fn test1() {
    let sample_rate = 1000;
    let seconds = 20;
    let song = include_bytes!("./test1.org");
    let mut player = OrgPlayBuilder::new()
        .with_sample_rate(sample_rate)
        .with_interpolation(NoInterp)
        .with_asset_provider(DummyProvider)
        .build(song)
        .unwrap();
    let mut buf = vec![0.0_f32; sample_rate as usize * seconds * 2];
    player.synth_stereo(&mut buf);
    let mut player = OrgPlayBuilder::new()
        .with_sample_rate(sample_rate)
        .with_interpolation(Linear)
        .with_asset_provider(DummyProvider)
        .build(song)
        .unwrap();
    let mut buf = vec![0.0_f32; sample_rate as usize * seconds];
    player.synth_mono(&mut buf);
}
