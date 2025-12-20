use criterion::{Criterion, criterion_group, criterion_main};
use orgorg::{CaveStoryAssetProvider, OrgPlayBuilder};
use std::hint::black_box;

struct ConstAsset;

impl CaveStoryAssetProvider for ConstAsset {
    #[inline(always)]
    fn wavetable(&self) -> &[u8; 25600] {
        include_bytes!("../wavetable.dat")
    }

    #[inline(always)]
    fn drum(&self) -> &[u8; 40000] {
        include_bytes!("../drums.dat")
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
                            .with_asset_provider(ConstAsset)
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
