// Well, orgorg crate(the actual player crate) has unsafe code.
// But at least let's make our innocent cli player free from unsafe.
#![forbid(unsafe_code)]

use std::{
    io::{Write, stdout},
    path::{Path, PathBuf},
    sync::{
        Arc, OnceLock,
        atomic::{AtomicBool, AtomicU32, AtomicU64, Ordering},
    },
    time::Duration,
};

use anyhow::{Context, Result};
use clap::{Args, Parser, Subcommand, ValueEnum};
use cpal::{
    Device, SampleRate, StreamConfig,
    traits::{DeviceTrait, HostTrait, StreamTrait},
};
use is_terminal::IsTerminal;
use orgorg::{CaveStoryAssetProvider, OrgInterpolation, OrgPlay, OrgPlayBuilder};
use ouroboros::self_referencing;

use crate::pxt::synth_pxt;

mod pxt;

static ASSET_BY_DUMP: OnceLock<AssetByDump> = OnceLock::new();

/// A player for Organya Music.
/// Requires original Doukutsu.exe from dou_1006.zip in the working directory.
#[derive(Parser)]
#[command(version, about, long_about = None)]
struct Cli {
    /// Specify Doukutsu.exe file
    #[arg(long)]
    exe: Option<PathBuf>,

    #[command(subcommand)]
    command: Commands,
}

#[derive(Args)]
struct AudioConfig {
    /// Output raw f32 audio data to stdout
    #[arg(long)]
    raw: bool,
    /// Mono output
    #[arg(long)]
    mono: bool,
    /// Sample rate
    #[arg(long, default_value = "48000")]
    rate: u32,
    /// Interpolation to use
    #[arg(long, value_enum, default_value = "lagrange")]
    interp: InterpModes,
}

#[derive(Subcommand)]
enum Commands {
    /// Dump wavetable and drums needed for OrgPlay
    Dump,
    /// Play .org music
    Play {
        path: PathBuf,
        #[command(flatten)]
        config: AudioConfig,
    },
}

#[derive(ValueEnum, Clone, Copy)]
enum InterpModes {
    Linear,
    None,
    Lagrange,
}

// Bad API design lol. Requires user to do this shit.
// Well, self-referential struct isn't that bad.
// But compile-time generics -> runtime polymorphism is painful.
#[self_referencing]
struct OwnedOrgPlay<I: OrgInterpolation, A: CaveStoryAssetProvider> {
    org: Vec<u8>,
    #[borrows(org)]
    #[covariant]
    player: OrgPlay<'this, I, A>,
}

trait DynOrgPlay: Send {
    fn synth_mono(&mut self, buf: &mut [f32]);
    fn synth_stereo(&mut self, buf: &mut [f32]);
    fn get_loop(&self) -> (u32, u32);
    fn get_beat(&self) -> u32;
}

impl<I: OrgInterpolation, A: CaveStoryAssetProvider + Send> DynOrgPlay for OwnedOrgPlay<I, A> {
    fn synth_mono(&mut self, buf: &mut [f32]) {
        self.with_player_mut(|player| player.synth_mono(buf));
    }
    fn synth_stereo(&mut self, buf: &mut [f32]) {
        self.with_player_mut(|player| player.synth_stereo(buf));
    }
    fn get_loop(&self) -> (u32, u32) {
        self.with_player(|player| player.get_loop())
    }
    fn get_beat(&self) -> u32 {
        self.with_player(|player| player.get_beat())
    }
}

fn make_dyn_orgplay(
    org: Vec<u8>,
    interp: InterpModes,
    sample_rate: u32,
) -> Result<Box<dyn DynOrgPlay>> {
    use orgorg::interp_impls;
    // At least we can use macro here.
    macro_rules! make {
        ($t:tt) => {
            Box::new(OwnedOrgPlay::try_new(org, |o| {
                OrgPlayBuilder::new()
                    .with_sample_rate(sample_rate)
                    .with_asset_provider(ASSET_BY_DUMP.get().unwrap())
                    .with_interpolation(interp_impls::$t)
                    .build(o)
                    .context("Invalid org music")
            })?)
        };
    }
    let res: Box<dyn DynOrgPlay> = match interp {
        InterpModes::Linear => make!(Linear),
        InterpModes::None => make!(NoInterp),
        InterpModes::Lagrange => make!(Lagrange),
    };
    Ok(res)
}

fn find_config(device: &Device, config: &AudioConfig) -> Result<StreamConfig> {
    let supported_configs_range = device.supported_output_configs()?;
    let channels = if config.mono { 1 } else { 2 };
    for supported_config in supported_configs_range {
        if supported_config.channels() != channels {
            continue;
        }
        if let Some(config) = supported_config.try_with_sample_rate(SampleRate(config.rate)) {
            return Ok(config.config());
        }
    }

    anyhow::bail!("Cannot find suitable config")
}

fn player_raw(config: &AudioConfig, org: Vec<u8>, mut write: impl Write) -> Result<()> {
    let mut player = make_dyn_orgplay(org, config.interp, config.rate)?;
    let mut buf = [0.0_f32; 4096];
    loop {
        if config.mono {
            player.synth_mono(&mut buf);
        } else {
            player.synth_stereo(&mut buf);
        }
        write.write_all(zerocopy::transmute_ref!(buf.as_slice()))?;
    }
}

fn player(
    device: &Device,
    config: StreamConfig,
    interp: InterpModes,
    org: Vec<u8>,
    control: Arc<PlayerControl>,
    exit: oneshot::Receiver<()>,
) -> Result<()> {
    let channels = config.channels;

    let mut player = make_dyn_orgplay(org, interp, config.sample_rate.0)?;
    let (loop_start, loop_end) = player.get_loop();
    control.loop_start.store(loop_start, Ordering::Relaxed);
    control.loop_end.store(loop_end, Ordering::Relaxed);

    let ctrl = control.clone();
    let stream = device.build_output_stream(
        &config,
        move |data: &mut [f32], _| {
            if ctrl.paused.load(Ordering::Relaxed) {
                return;
            }
            // Usually synthesis inside audio thread is bad idea.
            // But my player is very fast so not big of deal.
            match channels {
                1 => player.synth_mono(data),
                2 => player.synth_stereo(data),
                _ => (),
            }
            ctrl.played_samples
                .fetch_add(data.len() as u64, Ordering::Relaxed);
            ctrl.cur_beat.store(player.get_beat(), Ordering::Relaxed);
        },
        |err| {
            eprintln!("{err}");
        },
        None,
    )?;
    stream.play()?;

    // Don't care, received message either sender is dropped
    let _ = exit.recv();
    // Be explicit
    drop(stream);
    Ok(())
}

#[derive(Default)]
struct PlayerControl {
    paused: AtomicBool,
    cur_beat: AtomicU32,
    loop_start: AtomicU32,
    loop_end: AtomicU32,
    played_samples: AtomicU64,
}

#[derive(Debug)]
struct AssetByDump([u8; 25600], [u8; 40000]);

impl CaveStoryAssetProvider for &AssetByDump {
    fn wavetable(&self) -> &[u8; 25600] {
        &self.0
    }

    fn drum(&self) -> &[u8; 40000] {
        &self.1
    }
}

fn dump_and_synth(file: &Path) -> Result<AssetByDump> {
    // I know md5 is broken, but it should be okay for this purpose.
    const EXPECTED_MD5: [u8; 16] = [
        206, 57, 66, 219, 192, 70, 53, 244, 176, 24, 0, 111, 82, 60, 214, 244,
    ];
    let file = std::fs::read(file)?;
    let md = md5::compute(&file);
    if md.as_slice() != EXPECTED_MD5 {
        anyhow::bail!("Invalid Doukutsu.exe (checksum mismatch)");
    }

    let wavetable: [u8; 25600] = file
        .get(0x9b3a8..0xa17a8)
        .context("Cannot extract wavetable.dat")?
        .try_into()
        .unwrap();

    const PXTS: [(usize, usize); 6] = [
        (2, 0x0922d0), // 0x96
        (2, 0x0923b0), // 0x97
        (2, 0x092570), // 0x9a
        (1, 0x092490), // 0x98
        (1, 0x092500), // 0x99
        (2, 0x0929d0), // 0x9b
    ];
    let mut drums = vec![];
    for (channels, offset) in PXTS {
        let pxt = file
            .get(offset..offset + channels * 112)
            .context("Cannot find drum")?;
        drums.append(&mut synth_pxt(pxt));
    }
    let drums: [i8; 40000] = drums.try_into().ok().context("Invalid drums length")?;
    let drums: [u8; 40000] = zerocopy::transmute!(drums);

    Ok(AssetByDump(wavetable, drums))
}

fn main() -> Result<()> {
    let args = Cli::parse();
    let exe = args.exe.unwrap_or(PathBuf::from("./Doukutsu.exe"));
    if !std::fs::exists(&exe)? {
        anyhow::bail!("Cannot find {exe:?} in working directory.");
    }
    ASSET_BY_DUMP.set(dump_and_synth(&exe)?).unwrap();

    match args.command {
        Commands::Dump => {
            std::fs::write("./wavetable.dat", ASSET_BY_DUMP.get().unwrap().0.as_slice())?;
            println!("Wrote wavetables to ./wavetable.dat");
            std::fs::write("./drums.dat", ASSET_BY_DUMP.get().unwrap().1.as_slice())?;
            println!("Wrote drums to ./drums.dat");
            Ok(())
        }
        Commands::Play { path, config } => {
            let org = std::fs::read(path).context("Cannot open .org file")?;

            if config.raw {
                let stdout = stdout().lock();
                return player_raw(&config, org, stdout);
            }

            let interp = config.interp;
            let channels = if config.mono { 1 } else { 2 };
            let rate = config.rate;
            let control: Arc<PlayerControl> = Arc::default();
            let control_clone = control.clone();
            let (_exit, exit_receiver) = oneshot::channel();

            let device = cpal::default_host()
                .default_output_device()
                .context("Cannot find audio output device")?;
            let config = find_config(&device, &config)?;

            let join = std::thread::spawn(move || {
                player(&device, config, interp, org, control_clone, exit_receiver)
            });

            let mut stdout = stdout();
            let tick_rate = Duration::from_millis(50);
            loop {
                // Only print stat if it's terminal
                if stdout.is_terminal() {
                    let frames = control.played_samples.load(Ordering::Relaxed) / channels;
                    let secs = frames / rate as u64;
                    let milis = (frames % rate as u64) as f64 / rate as f64;
                    let milis = &format!("{milis:.2}")[2..];
                    write!(
                        stdout,
                        "\x1b[2K{secs:>3}.{milis}s || Beat {}/{}\r",
                        control.cur_beat.load(Ordering::Relaxed),
                        control.loop_end.load(Ordering::Relaxed)
                    )?;
                    stdout.flush()?;
                }

                if join.is_finished() {
                    return join.join().unwrap();
                }

                std::thread::sleep(tick_rate);
            }
        }
    }
}
