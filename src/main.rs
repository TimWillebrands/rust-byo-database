use std::fs;
use std::io;
use std::cell::Cell;
use byteorder::{ByteOrder, LittleEndian};

const HEADER: i16 = 4;
const BTREE_PAGE_SIZE: usize = 4096;
const BTREE_MAX_KEY_SIZE: i16 = 1000;
const BTREE_MAX_VAL_SIZE: i16 = 3000;

const BNODE_NODE: i8 = 1; // internal nodes without values
const BNODE_LEAF: i8 = 2; // leaf nodes with values

fn save_data(path: &str, data: String) -> io::Result<()> {
    let random_int = rand::random::<u16>();
    let tmp = format!("{path}.tmp.{random_int}");

    fs::write(tmp.clone(), data)?;
    fs::rename(tmp, path)?;
    
    Ok(())
}

fn main() {
    // let tree: BTree = {
    //
    // }
    println!("Hoi {HEADER}");
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
    fn get_data_slice(&self, from: usize) -> [u8;2] {
        let mut slice: [u8; 2] = [0; 2]; // Create a fixed-size array of length 2
        for (i, cell) in self.data.iter().enumerate().skip(from).take(2) {
            slice[i - from] = cell.get();
        }
        slice
    }
    pub fn btype(&self) -> u16 {
        let slice = self.get_data_slice(0);
        LittleEndian::read_u16(&slice)
    }
    pub fn nkeys(&self) -> u16 {
        let slice = self.get_data_slice(2);
        LittleEndian::read_u16(&slice)
    }
    // pub fn set_header(&self, btype: u16, nkeys: u16) {
    //     &self.data[0] 
    // } 
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
}
