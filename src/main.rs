use std::fs;
use std::io;
use std::cell::Cell;
use byteorder::{ByteOrder, LittleEndian};

const HEADER: u16 = 4;
const BTREE_PAGE_SIZE: usize = 4096;
const BTREE_MAX_KEY_SIZE: u16 = 1000;
const BTREE_MAX_VAL_SIZE: u16 = 3000;

const BNODE_NODE: u8 = 1; // internal nodes without values
const BNODE_LEAF: u8 = 2; // leaf nodes with values

fn save_data(path: &str, data: String) -> io::Result<()> {
    let random_int = rand::random::<u16>();
    let tmp = format!("{path}.tmp.{random_int}");

    fs::write(tmp.clone(), data)?;
    fs::rename(tmp, path)?;
    
    Ok(())
}

fn main() {
    let data = core::array::from_fn::<Cell<u8>, {BTREE_PAGE_SIZE}, _>
        (|_i| Cell::new(0));
    let bnode = BNode { data };

    bnode.set_header(BNODE_LEAF.into(), 4);
    let _ = bnode.set_ptr(4, 69420);
    let hi = bnode.get_ptr(4);

    let stuff = bnode.data
        .iter()
        .map(|cell| cell.get().to_string())
        .collect::<Vec<_>>()
        .join(",");

    println!("Hello {}", stuff);
}

struct BNode {
    data: [Cell<u8>; BTREE_PAGE_SIZE]
}

struct BTree {
    root: u64
}

impl BTree {
    // pub fn get() -> BNode {
    // 
    // }
    // pub fn new() -> BNode {
    // 
    // }
    // pub fn del() -> BNode {
    // 
    // }
}

impl BNode {
    fn get_data_slice_u16(&self, from: usize) -> [u8;2] {
        let mut slice: [u8; 2] = [0; 2]; // Create a fixed-size array of length 2
        for (i, cell) in self.data.iter().enumerate().skip(from).take(2) {
            slice[i - from] = cell.get();
        }
        slice
    }
    fn get_data_slice_u64(&self, from: usize) -> [u8;8] {
        let mut slice: [u8; 8] = [0; 8]; // Create a fixed-size array of length 2
        for (i, cell) in self.data.iter().enumerate().skip(from).take(8) {
            slice[i - from] = cell.get();
        }
        slice
    }
    pub fn btype(&self) -> u16 {
        let slice = self.get_data_slice_u16(0);
        LittleEndian::read_u16(&slice)
    }
    pub fn nkeys(&self) -> u16 {
        let slice = self.get_data_slice_u16(2);
        LittleEndian::read_u16(&slice)
    }
    pub fn set_header(&self, btype: u16, nkeys: u16) {
        let btype_b1: u8 = (btype & 0xFF) as u8;        // Lower 8 bits
        let btype_b2: u8 = ((btype >> 8) & 0xFF) as u8; // Upper 8 bits
        let _ = &self.data[0].set(btype_b1); 
        let _ = &self.data[1].set(btype_b2); 

        let nkeys_b1: u8 = (nkeys & 0xFF) as u8;        // Lower 8 bits
        let nkeys_b2: u8 = ((nkeys >> 8) & 0xFF) as u8; // Upper 8 bits
        let _ = &self.data[2].set(nkeys_b1); 
        let _ = &self.data[3].set(nkeys_b2); 
    } 
    pub fn get_ptr(&self, idx: u16) -> Result<u64, ()> {
        if idx >= self.nkeys() {
            return Err(());
        }

        let pos = HEADER + 8 * idx;
        let slice = self.get_data_slice_u64(pos.into());
        Ok(LittleEndian::read_u64(&slice))
    }
    pub fn set_ptr(&self, idx: u16, val: u64) -> Result<u64, ()> {
        if idx >= self.nkeys() {
            return Err(());
        }

        let pos:usize = (HEADER + 8 * idx).into();
        for (i, cell) in self.data.iter().enumerate().skip(pos).take(8) {
            cell.set(((val >> (i-pos)*8) & 0xFF) as u8);
        }

        Ok(val)
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn constraints() {
        let node1max = super::HEADER + 8 + 2 + 4 
            + super::BTREE_MAX_KEY_SIZE 
            + super::BTREE_MAX_VAL_SIZE;
        assert!(node1max <= super::BTREE_PAGE_SIZE.try_into().unwrap()); 
    }

    #[test]
    fn btype_access() {
        use std::cell::Cell;

        let data = core::array::from_fn::<Cell<u8>, {super::BTREE_PAGE_SIZE}, _>
            (|i| Cell::new(((i + 1) % 255).try_into().unwrap()));
        let bnode = super::BNode { data };
        assert_eq!(bnode.btype(), 513); 
    }

    #[test]
    fn nkeys_access() {
        use std::cell::Cell;

        let data = core::array::from_fn::<Cell<u8>, {super::BTREE_PAGE_SIZE}, _>
            (|i| Cell::new(((i + 1) % 255).try_into().unwrap()));
        let bnode = super::BNode { data };
        assert_eq!(bnode.nkeys(), 1027); 
    }

    #[test]
    fn set_header() {
        use std::cell::Cell;

        let data = core::array::from_fn::<Cell<u8>, {super::BTREE_PAGE_SIZE}, _>
            (|i| Cell::new(((i + 1) % 255).try_into().unwrap()));
        let bnode = super::BNode { data };

        bnode.set_header(69, 420);

        assert_eq!(bnode.btype(), 69); 
        assert_eq!(bnode.nkeys(), 420); 
    }

    #[test]
    fn set_and_get_ptr() {
        use std::cell::Cell;

        let data = core::array::from_fn::<Cell<u8>, {super::BTREE_PAGE_SIZE}, _>
            (|_i| Cell::new(0));
        let bnode = super::BNode { data };

        bnode.set_header(super::BNODE_LEAF.into(), 4);
        let _ = bnode.set_ptr(4, 69420);

        assert_eq!(bnode.get_ptr(4).unwrap(), 69420); 
    }
}
