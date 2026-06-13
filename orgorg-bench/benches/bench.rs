use criterion::{Criterion, criterion_group, criterion_main};
use orgorg::{CaveStoryAssetProvider, OrgPlayBuilder, wt};
use std::hint::black_box;

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

fn criterion_benchmark(c: &mut Criterion) {
    let names = [
        "Access.org",
        // "Balcony.org",
        // "Balrog's Theme.org",
        // "Break Down.org",
        "Cave Story.org",
        // "Cemetery (Internal Percussion).org",
        // "Cemetery.org",
        // "Charge.org",
        // "Gameover.org",
        // "Eyes of Flame.org",
        "Geothermal.org",
        // "Gestation (Internal Percussion).org",
        // "Gestation.org",
        // "Get Heart Tank!.org",
        // "Got Item! (Internal Percussion).org",
        // "Got Item!.org",
        // "Gravity (Internal Percussion).org",
        // "Gravity.org",
        // "Halloween 2.org",
        // "Hero's End.org",
        // "Jenka 1.org",
        // "Jenka 2.org",
        // "Last Battle.org",
        // "Last Cave.org",
        // "Living Waterway (Internal Percussion).org",
        // "Labyrinth Fight.org",
        // "Living Waterway.org",
        // "Meltdown 2.org",
        // "Meltdown.org",
        "Mimiga Town.org",
        // "Mischievous Robot.org",
        "Moonsong.org",
        "On to Grasstown.org",
        // "Oppression.org",
        // "People of the Root (Internal Percussion).org",
        // "People of the Root.org",
        // "Pier Walk.org",
        // "Plant.org",
        // "Pulse.org",
        // "Quiet.org",
        // "Running Hell.org",
        // "Run!.org",
        // "Safety.org",
        // "Scorching Back.org",
        // "Seal Chamber.org",
        // "The Way Back Home (Internal Percussion).org",
        // "The Way Back Home.org",
        // "Toroko's Theme.org",
        // "Tyrant.org",
        // "Untitled (Rockorg).org",
        // "White (Internal Percussion).org",
        // "Victory!.org",
        // "White.org",
        // "Wind Fortress.org",
        // "XXXX.org",
        // "Zombie.org",
    ];
    for song in names {
        let data = &std::fs::read(format!("org/{song}")).unwrap();
        c.bench_function(song, |b| {
            b.iter_batched(
                || {
                    (
                        OrgPlayBuilder::new()
                            .with_soundbank_provider(ConstAsset)
                            .build(data)
                            .unwrap(),
                        vec![0.0_f32; 4096],
                    )
                },
                |(mut o, mut b)| {
                    for _ in 0..(48000 * 100 / 4096) {
                        o.synth_stereo(&mut b);
                        black_box(&mut b);
                    }
                },
                criterion::BatchSize::LargeInput,
            );
        });
    }
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
