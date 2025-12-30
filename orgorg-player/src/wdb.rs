use orgorg::Soundbank;
use self_cell::self_cell;

// My API is painful for advanced uses. It needs self-referential structs.
type OwnedSoundbankRef<'a> = (&'a [u8; 25600], Box<[&'a [i8]]>);

self_cell!(
    pub struct OwnedSoundbank {
        owner: Box<[u8]>,
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
pub fn from_soundbank_wdb(mut wdb: Vec<u8>) -> Option<OwnedSoundbank> {
    fn fix_samples(wdb: &mut [u8]) -> Option<usize> {
        if wdb.len() < 25600 {
            return None;
        }
        let mut cnt = 0;
        let mut offset = 25600;
        while offset < wdb.len() {
            let len = u32::from_le_bytes(wdb.get(offset..offset + 4)?.try_into().unwrap()) as usize;
            let slice: &mut [i8] =
                zerocopy::transmute_mut!(wdb.get_mut(offset + 4..offset + 4 + len)?);
            slice
                .iter_mut()
                .for_each(|v| *v = v.wrapping_sub_unsigned(0x80));
            offset += 4 + len;
            cnt += 1;
        }
        if offset == wdb.len() { Some(cnt) } else { None }
    }
    let cnt = fix_samples(&mut wdb)?;
    Some(OwnedSoundbank::new(wdb.into_boxed_slice(), |v| {
        let wavetable = v[0..25600].try_into().unwrap();
        let mut drums = Vec::with_capacity(cnt);
        let mut offset = 25600;
        while offset < v.len() {
            let len = u32::from_le_bytes(v[offset..offset + 4].try_into().unwrap()) as usize;
            let slice = &v[offset + 4..offset + 4 + len];
            drums.push(zerocopy::transmute_ref!(slice));
            offset += len + 4;
        }
        (wavetable, drums.into_boxed_slice())
    }))
}
