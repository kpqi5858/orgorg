use orgorg::{CaveStoryAssetProvider, OrgPlayBuilder, interp_impls::NoInterp};

struct DummyProvider;

impl CaveStoryAssetProvider for DummyProvider {
    fn wavetable(&self) -> &[u8; 25600] {
        &[0; 25600]
    }
    fn drum(&self) -> &[u8; 40000] {
        &[0; 40000]
    }
}

#[test]
fn access() {
    let org = include_bytes!("../org/Access.org");
    let mut player = OrgPlayBuilder::new()
        .with_interpolation(NoInterp)
        .with_sample_rate(1000)
        .with_asset_provider(DummyProvider)
        .build(org)
        .unwrap();
    let mut buf = vec![0.0_f32; 1000 * 30 * 2];
    player.synth_stereo(&mut buf);
}

#[test]
fn geothermal() {
    let org = include_bytes!("../org/Geothermal.org");
    let mut player = OrgPlayBuilder::new()
        .with_interpolation(NoInterp)
        .with_sample_rate(1000)
        .with_asset_provider(DummyProvider)
        .build(org)
        .unwrap();
    let mut buf = vec![0.0_f32; 1000 * 75];
    player.synth_mono(&mut buf);
}
