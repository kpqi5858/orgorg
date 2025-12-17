use zerocopy::FromBytes;
use zerocopy::byteorder::little_endian as le;

#[derive(FromBytes)]
#[repr(C)]
struct Waveform {
    model: le::I32,
    _padding: [u8; 4],
    pitch: le::F64,
    level: le::I32,
    offset: le::I32,
}

#[derive(FromBytes)]
#[repr(C)]
struct PxtChannel {
    enabled: le::I32,
    length: le::I32,
    carrier: Waveform,
    frequency: Waveform,
    amplitude: Waveform,
    initial: le::I32,
    time_a: le::I32,
    value_a: le::I32,
    time_b: le::I32,
    value_b: le::I32,
    time_c: le::I32,
    value_c: le::I32,
    _padding: [u8; 4],
}

/// Generated from this code:
/// ```cpp
/// int8_t Waveforms[6][256];
/// for (uint32_t seed = 0, i = 0; i < 256; ++i) {
///   seed = (seed * 214013) + 2531011;                       // Linear congruential generator
///   Waveforms[0][i] = 0x40 * std::sin(i * 3.1416 / 0x80);   // Sine
///   Waveforms[1][i] = ((0x40 + i) & 0x80) ? 0x80 - i : i;   // Triangle
///   Waveforms[2][i] = -0x40 + i / 2;                        // Sawtooth up
///   Waveforms[3][i] = 0x40 - i / 2;                         // Sawtooth down
///   Waveforms[4][i] = 0x40 - (i & 0x80);                    // Square
///   Waveforms[5][i] = (int8_t)(seed >> 16) / 2;             // Pseudorandom
/// }
/// ```
const PXT_WAVEFORMS: [[i8; 256]; 6] = zerocopy::transmute!(*include_bytes!("./pixtone_ref.dat"));

impl PxtChannel {
    fn synth(&self) -> Vec<i32> {
        if self.enabled.get() == 0 {
            return Vec::new();
        }

        let nsamples = self.length.get() as usize;
        let mut result = Vec::with_capacity(nsamples);
        let get_wave_value = |w: &Waveform, phase: f64| -> i32 {
            let idx = (phase as i32) & 0xFF;
            let model = w.model.get() as usize;
            let val = PXT_WAVEFORMS[model][idx as usize] as i32;
            val * w.level.get()
        };
        let evaluate_env = |i: i32| -> i32 {
            let initial = self.initial.get();
            let points = [
                (self.time_a.get(), self.value_a.get()),
                (self.time_b.get(), self.value_b.get()),
                (self.time_c.get(), self.value_c.get()),
            ];
            let mut prevval = initial;
            let mut prevtime = 0;
            let mut nextval = 0;
            let mut nexttime = 256;

            for &(pt_time, pt_val) in points.iter().rev() {
                if i < pt_time {
                    nexttime = pt_time;
                    nextval = pt_val;
                }
            }
            for &(pt_time, pt_val) in points.iter() {
                if i >= pt_time {
                    prevtime = pt_time;
                    prevval = pt_val;
                }
            }
            if nexttime <= prevtime {
                return prevval;
            }
            (i - prevtime) * (nextval - prevval) / (nexttime - prevtime) + prevval
        };

        let c = &self.carrier;
        let f = &self.frequency;
        let a = &self.amplitude;

        let mut mainpos = c.offset.get() as f64;
        let maindelta = 256.0 * c.pitch.get() / (nsamples as f64);

        for i in 0..nsamples {
            let s = |p: f64| -> f64 { 256.0 * p * (i as f64) / (nsamples as f64) };
            let freq_phase = f.offset.get() as f64 + s(f.pitch.get());
            let freqval = get_wave_value(f, freq_phase);
            let amp_phase = a.offset.get() as f64 + s(a.pitch.get());
            let ampval = get_wave_value(a, amp_phase);
            let mainval = get_wave_value(c, mainpos);
            let env_val = evaluate_env(s(1.0) as i32);

            let term1 = ampval as i64 + 4096;
            let term2 = (mainval as i64 * term1) / 4096;
            let final_val = (term2 * env_val as i64) / 4096;
            result.push(final_val as i32);

            let denom = if freqval < 0 { 8192.0 } else { 2048.0 };
            mainpos += maindelta * (1.0 + (freqval as f64 / denom));
        }

        result
    }
}

pub fn synth_pxt(data: &[u8]) -> Vec<i8> {
    let res: Vec<_> = data
        .chunks_exact(112)
        .map(|v| {
            let v: [u8; 112] = v.try_into().unwrap();
            let pxt: PxtChannel = zerocopy::transmute!(v);
            pxt.synth()
        })
        .collect();
    let max_len = res.iter().map(|m| m.len()).max().unwrap();
    let mut ret = vec![0; max_len];
    for (idx, v) in ret.iter_mut().enumerate() {
        *v += res.iter().flat_map(|p| p.get(idx)).sum::<i32>() as i8;
    }
    ret
}
