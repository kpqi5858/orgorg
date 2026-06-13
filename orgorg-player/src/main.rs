// Well, orgorg crate(the actual player crate) has unsafe code.
// But at least let's make our innocent cli player free from unsafe.
#![forbid(unsafe_code)]

use std::{
    io::{Write, stderr, stdout},
    path::{Path, PathBuf},
    sync::{
        Arc,
        atomic::{AtomicBool, AtomicU32, AtomicU64, Ordering},
        mpsc,
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
use orgorg::{OrgPlay, OrgPlayBuilder, OrgSmp, PlayResult, PlayTill, Soundbank};
use self_cell::self_cell;

use crate::{
    pxt::synth_pxt,
    wdb::{OwnedSoundbank, from_soundbank_wdb},
};

mod pxt;
mod wdb;

/// A player for Organya Music.
/// Requires soundbank.wdb, or original Doukutsu.exe from dou_1006.zip in the working directory
#[derive(Parser)]
#[command(version, about, long_about = None)]
struct Cli {
    /// Specify Doukutsu.exe, or soundbank.wdb file
    #[arg(long)]
    sound: Option<PathBuf>,

    #[command(subcommand)]
    command: Commands,
}

#[derive(Args)]
struct AudioConfig {
    /// Output raw f32 audio data to stdout
    #[arg(long)]
    raw: bool,
    /// Mono output
    #[arg(long, short)]
    mono: bool,
    /// Sample rate
    #[arg(long, short, default_value = "48000")]
    rate: u32,
    /// Interpolation to use
    #[arg(long, short, value_enum, default_value = "lagrange")]
    interp: InterpModes,
    /// How many loops to play
    #[arg(long, short)]
    loops: Option<u32>,
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

#[derive(Default)]
struct PlayerControl {
    paused: AtomicBool,
    cur_beat: AtomicU32,
    loop_start: AtomicU32,
    loop_end: AtomicU32,
    played_samples: AtomicU64,
}

struct AssetByDump([i8; 25600], [i8; 40000]);

trait DynOrgPlay: Send {
    fn synth_mono_till(&mut self, buf: &mut [f32], till: PlayTill) -> PlayResult;
    fn synth_stereo_till(&mut self, buf: &mut [f32], till: PlayTill) -> PlayResult;
    fn get_loop(&self) -> (u32, u32);
    fn get_beat(&self) -> u32;
}

fn make_dyn_orgplay(
    org: Vec<u8>,
    soundbank: OwnedSoundbank,
    interp: InterpModes,
    sample_rate: u32,
) -> Result<Box<dyn DynOrgPlay>> {
    use orgorg::interp_impls;
    macro_rules! make {
        ($t:ident) => {{
            type _OrgPlay<'a> = OrgPlay<'a, interp_impls::$t, Soundbank<'a>>;
            self_cell!(
                struct _ImplDetail {
                    owner: (Box<[u8]>, OwnedSoundbank),
                    #[covariant]
                    dependent: _OrgPlay,
                }
            );
            impl DynOrgPlay for _ImplDetail {
                fn synth_mono_till(&mut self, buf: &mut [f32], till: PlayTill) -> PlayResult {
                    self.with_dependent_mut(|_, m| m.synth_mono_till(buf, till))
                }

                fn synth_stereo_till(&mut self, buf: &mut [f32], till: PlayTill) -> PlayResult {
                    self.with_dependent_mut(|_, m| m.synth_stereo_till(buf, till))
                }

                fn get_loop(&self) -> (u32, u32) {
                    self.with_dependent(|_, m| m.get_loop())
                }

                fn get_beat(&self) -> u32 {
                    self.with_dependent(|_, m| m.get_beat())
                }
            }
            Box::new(_ImplDetail::try_new(
                (org.into_boxed_slice(), soundbank),
                |a| {
                    OrgPlayBuilder::new()
                        .with_sample_rate(sample_rate)
                        .with_soundbank_provider(a.1.make_soundbank())
                        .with_interpolation(interp_impls::$t)
                        .build(&a.0)
                        .context("Invalid org music")
                },
            )?)
        }};
    }

    let i: Box<dyn DynOrgPlay> = match interp {
        InterpModes::Linear => make!(Linear),
        InterpModes::Lagrange => make!(Lagrange),
        InterpModes::None => make!(NoInterp),
    };
    Ok(i)
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

    anyhow::bail!("Cannot find suitable audio output config")
}

fn handle_synthesis(
    player: &mut dyn DynOrgPlay,
    mut buf: &mut [f32],
    mono: bool,
    loops: &mut Option<u32>,
) -> Option<usize> {
    let till = match loops {
        Some(_) => PlayTill::Loop,
        None => PlayTill::Endless,
    };
    let original_len = buf.len();
    while !buf.is_empty() {
        let res = if mono {
            player.synth_mono_till(buf, till)
        } else {
            player.synth_stereo_till(buf, till)
        };
        buf = &mut buf[res.filled_length()..];
        if res.reached_end() {
            let loops = loops.as_mut().unwrap();
            if *loops == 0 {
                return Some(original_len - buf.len());
            }
            *loops -= 1;
        }
    }

    None
}

fn player_raw(
    config: &AudioConfig,
    soundbank: OwnedSoundbank,
    org: Vec<u8>,
    mut write: impl Write,
) -> Result<()> {
    let mut player = make_dyn_orgplay(org, soundbank, config.interp, config.rate)?;
    let mut buf = vec![0.0_f32; 4096];
    let mut loops = config.loops;
    loop {
        let res = handle_synthesis(&mut *player, &mut buf, config.mono, &mut loops);
        write.write_all(zerocopy::transmute_ref!(&buf[..res.unwrap_or(buf.len())]))?;
        if res.is_some() {
            return Ok(());
        }
    }
}

fn player(
    device: &Device,
    soundbank: OwnedSoundbank,
    config: StreamConfig,
    interp: InterpModes,
    mut loops: Option<u32>,
    org: Vec<u8>,
    control: Arc<PlayerControl>,
    exit_send: mpsc::Sender<()>,
    exit_recv: mpsc::Receiver<()>,
) -> Result<()> {
    let channels = config.channels;

    let mut player = make_dyn_orgplay(org, soundbank, interp, config.sample_rate.0)?;
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
            let res = handle_synthesis(&mut *player, data, channels == 1, &mut loops);
            if res.is_some() {
                ctrl.paused.store(true, Ordering::Relaxed);
                exit_send.send(()).unwrap();
            }
            ctrl.played_samples
                .fetch_add(res.unwrap_or(data.len()) as u64, Ordering::Relaxed);
            ctrl.cur_beat.store(player.get_beat(), Ordering::Relaxed);
        },
        |err| {
            eprintln!("{err}");
        },
        None,
    )?;
    stream.play()?;

    let _ = exit_recv.recv();
    // Be explicit
    drop(stream);
    Ok(())
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

    Ok(AssetByDump(zerocopy::transmute!(wavetable), drums))
}

fn to_soundbank(asset: AssetByDump) -> OwnedSoundbank {
    let mut data = Vec::with_capacity(25600 + 40000);
    data.extend(asset.0.into_iter().map(|v| v as OrgSmp));
    data.extend(asset.1.into_iter().map(|v| v as OrgSmp));
    OwnedSoundbank::new(data.into_boxed_slice(), |d| {
        let (wavetable, drums) = d.split_at(25600);
        let drums = Box::new([
            &drums[0..5000],
            &[],
            &drums[5000..15000],
            &[],
            &drums[15000..25000],
            &drums[25000..26000],
            &drums[26000..36000],
            &[],
            &drums[36000..40000],
        ]);
        (wavetable.try_into().unwrap(), drums)
    })
}

// If user specified path, first try as Doukutsu.exe, then try as wdb
// Else, first try ./soundbank.wdb, then try ./Doukutsu.exe
fn determine_soundbank(sound: Option<&Path>) -> Result<OwnedSoundbank> {
    let soundbank = match sound {
        Some(path) => match dump_and_synth(path) {
            Ok(asset) => {
                eprintln!("Using original Cave Story sounds");
                to_soundbank(asset)
            }
            Err(err) => {
                eprintln!("Using soundbank from {}", path.to_string_lossy());
                let wdb = std::fs::read(path)?;
                from_soundbank_wdb(wdb)
                    .context(err.context(format!(
                        "Tried but failed to extract sound from {} as Doukutsu.exe",
                        path.to_string_lossy()
                    )))
                    .context("Invalid wdb")?
            }
        },
        None => {
            let wdb = std::fs::read("./soundbank.wdb");
            if let Ok(wdb) = wdb {
                eprintln!("Using soundbank from ./soundbank.wdb");
                from_soundbank_wdb(wdb).context("Invalid wdb")?
            } else {
                let path = PathBuf::from("./Doukutsu.exe");
                if path.exists() {
                    eprintln!("Using original Cave Story sounds");
                    to_soundbank(dump_and_synth(&path)?)
                } else {
                    anyhow::bail!(
                        "Cannot find soundbank.wdb or Doukutsu.exe from working directory. Please specify with --sound argument."
                    )
                }
            }
        }
    };
    Ok(soundbank)
}

fn main() -> Result<()> {
    let args = Cli::parse();

    match args.command {
        Commands::Dump => {
            let exe = args.sound.unwrap_or(PathBuf::from("./Doukutsu.exe"));
            let asset_by_dump =
                dump_and_synth(&exe).context("Cannot extract sound from Doukutsu.exe")?;
            let data: &[u8] = zerocopy::transmute_ref!(asset_by_dump.0.as_slice());
            std::fs::write("./wavetable.dat", data)?;
            println!("Wrote wavetables to ./wavetable.dat");
            let data: &[u8] = zerocopy::transmute_ref!(asset_by_dump.1.as_slice());
            std::fs::write("./drums.dat", data)?;
            println!("Wrote drums to ./drums.dat");
            Ok(())
        }
        Commands::Play { path, config } => {
            if config.rate < 1000 {
                anyhow::bail!("Sample rate cannot be less than 1000");
            }
            let soundbank = determine_soundbank(args.sound.as_deref())?;
            let org = std::fs::read(path).context("Cannot open .org file")?;

            if config.raw {
                let stdout = stdout().lock();
                return player_raw(&config, soundbank, org, stdout);
            }

            let loops = config.loops;
            let interp = config.interp;
            let channels = if config.mono { 1 } else { 2 };
            let rate = config.rate;
            let control: Arc<PlayerControl> = Arc::default();
            let control_clone = control.clone();
            let (exit_send, exit_recv) = mpsc::channel();

            let device = cpal::default_host()
                .default_output_device()
                .context("Cannot find audio output device")?;
            let config = find_config(&device, &config)?;

            let join = std::thread::spawn(move || {
                player(
                    &device,
                    soundbank,
                    config,
                    interp,
                    loops,
                    org,
                    control_clone,
                    exit_send,
                    exit_recv,
                )
            });

            let mut stdout = stderr();
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
