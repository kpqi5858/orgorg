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
fn access_org() {
    let org = include_bytes!("../org/Access.org");
    let mut player = OrgPlayBuilder::new()
        .with_interpolation(NoInterp)
        .with_sample_rate(10000)
        .with_asset_provider(DummyProvider)
        .build(org);
    let mut buf = vec![0.0_f32; 10000 * 15 * 2];
    player.synth_stereo(&mut buf);
}
