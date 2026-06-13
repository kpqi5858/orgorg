use orgorg::{OrgSmp, Soundbank};
use self_cell::self_cell;

type OwnedSoundbankRef<'a> = (&'a [OrgSmp; 25600], Box<[&'a [OrgSmp]]>);

self_cell!(
    pub struct OwnedSoundbank {
        owner: Box<[OrgSmp]>,
        #[covariant]
        dependent: OwnedSoundbankRef,
    }
);

impl OwnedSoundbank {
    pub fn make_soundbank<'a>(&'a self) -> Soundbank<'a> {
        Soundbank::new(self.borrow_dependent().0, &self.borrow_dependent().1)
    }
}

/// Make OwnedSoundbank from `soundbank.wdb`. Return None for invalid soundbank.
///
/// File format is:
/// - 25600 bytes of wavetable
/// - Until end of the file:
///   - Wave length N in u32 little-endian.
///   - Followed by N length i8 wave data. Need to subtract 0x80 for each sample.
pub fn from_soundbank_wdb(wdb: Vec<u8>) -> Option<OwnedSoundbank> {
    if wdb.len() < 25600 {
        return None;
    }
    let mut data = vec![];
    data.extend(wdb[0..25600].iter().map(|v| *v as i8 as OrgSmp));
    let mut len = vec![];
    let mut offset = 25600;
    while offset < wdb.len() {
        let cur_len = u32::from_le_bytes(wdb.get(offset..offset + 4)?.try_into().unwrap()) as usize;
        let slice = wdb.get(offset + 4..offset + 4 + cur_len)?;
        data.extend(slice.iter().map(|v| v.wrapping_sub(0x80) as i8 as OrgSmp));
        offset += 4 + cur_len;
        len.push(cur_len);
    }
    if offset != wdb.len() {
        return None;
    }

    Some(OwnedSoundbank::new(data.into_boxed_slice(), |data| {
        let (wavetable, mut drums) = data.split_at(25600);
        let wavetable = wavetable.try_into().unwrap();
        let drums_arr = len.iter().map(|v| {
            let (a, b) = drums.split_at(*v);
            drums = b;
            a
        });
        (wavetable, drums_arr.collect())
    }))
}
