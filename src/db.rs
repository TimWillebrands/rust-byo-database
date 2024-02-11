const HEADER: u32 = 4;
const BTREE_PAGE_SIZE: u32 = 4096;
const BTREE_MAX_KEY_SIZE: u32 = 1000;
const BTREE_MAX_VAL_SIZE: u32 = 3000;

#[derive(Debug)]
pub enum BNodeType {
    Node,
    Leaf,
}

impl BNodeType {
    pub fn as_u16(&self) -> u16 {
        match *self {
            BNodeType::Node => 1,
            BNodeType::Leaf => 2,
        }
    }
}

//  | type | nkeys |  pointers  |   offsets  | key-values
//  |  2B  |   2B  | nkeys * 8B | nkeys * 2B | ...
pub struct BNode {
    data: Vec<u8>, // can be dumped to the disk
}

pub struct BTree {
    // pointer (a nonzero page number)
    root: u64,
    // callbacks for managing on-disk pages
    // get func(uint64) BNode // dereference a pointer
    // new func(BNode) uint64 // allocate a new page
    // del func(uint64)       // deallocate a page
}

impl BNode {
    pub fn new(typ: BNodeType, keys: u16) -> BNode {
        let [type_high, type_low] = typ.as_u16().to_le_bytes();
        let [keys_high, keys_low] = keys.to_le_bytes();

        let required_size = usize::from((HEADER as u16) + 8*keys + 2*keys);
        let mut data = vec![type_high, type_low, keys_high, keys_low];
        data.resize(required_size.into(), 0);

        return BNode { data };
    }

    pub fn btype(&self) -> Result<BNodeType, String> {
        let bytes: [u8; 2] = self.data[0..2]
            .try_into()
            .expect("type slice with incorrect length");

        let typ = u16::from_le_bytes(bytes);

        match typ {
            1 => Ok(BNodeType::Node),
            2 => Ok(BNodeType::Leaf),
            _ => Err("Unrecognised node type!".to_string()),
        }
    }

    pub fn nkeys(&self) -> u16 {
        let bytes: [u8; 2] = self.data[2..4]
            .try_into()
            .expect("keys slice with incorrect length");

        u16::from_le_bytes(bytes)
    }

    pub fn set_header(&mut self, typ: BNodeType, keys: u16) {
        let [type_high, type_low] = typ.as_u16().to_le_bytes();
        let [keys_high, keys_low] = keys.to_le_bytes();

        // let offset = usize::from((HEADER as u16) + 8*self.nkeys() + 2*(idx-1));
        let required_size = usize::from((HEADER as u16) + 8*keys + 2*keys);
        self.data.resize(required_size.into(), 0);

        self.data[0] = type_high;
        self.data[1] = type_low;
        self.data[2] = keys_high;
        self.data[3] = keys_low;
    }

    pub fn get_ptr(&self, idx: u16) -> Result<u64, String> {
        if idx >= self.nkeys() {
            return Err("Index out of bounds".to_string());
        }
        let pos = usize::from((HEADER as u16) + 8 * idx);

        if pos + 8 > self.data.len() {
            return Err("Index out of data range".to_string());
        }

        // Safely extract a u64 from the data slice
        let ptr_bytes = &self.data[pos..pos + 8]
            .try_into()
            .expect("slice with incorrect length");
        let ptr = u64::from_le_bytes(*ptr_bytes);

        Ok(ptr)
    }
    
    pub fn set_ptr(&mut self, idx:u16, val:u64) -> Result<(), String> {
        if idx >= self.nkeys() {
            return Err("Index out of bounds".to_string());
        }
        let pos = usize::from((HEADER as u16) + 8 * idx);
        
        let mut val_bytes = val.to_le_bytes();
        let slice = &mut self.data[pos..pos+8];

        slice.swap_with_slice(&mut val_bytes);

        return Ok(());
    }

    fn offset(&self, idx: u16) -> [u8; 2] {
        let offset = usize::from((HEADER as u16) + 8*self.nkeys() + 2*(idx-1));
        self.data[offset..offset+2]
            .try_into()
            .expect("Offset was not right size? 2 bytes")
    }

    fn offset_mut(&mut self, idx: u16) -> &mut [u8] {
        let offset = usize::from((HEADER as u16) + 8*self.nkeys() + 2*(idx-1));
        &mut self.data[offset..offset+2]
    }

    pub fn get_offset(&self, idx: u16) -> Result<u16, String> {
        if idx >= self.nkeys() {
            return Err("Index out of bounds".to_string());
        }

        match idx {
            0 => Ok(0),
            _ => Ok(u16::from_le_bytes(self.offset(idx)))
        }
    }

    pub fn set_offset(&mut self, idx: u16, offset:u16) -> Result<(), String>  {
        if idx == 0 {
            return Err("Plz no touching the 0th offset".to_string());
        }

        let off= self.offset_mut(idx);
        let mut val = offset.to_le_bytes();

        off.swap_with_slice(&mut val);
        
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn headers_stay_the_same() {
        let node = BNodeType::Node;
        let leaf = BNodeType::Leaf;
        assert_eq!(node.as_u16(), 1);
        assert_eq!(leaf.as_u16(), 2);
    }

    #[test]
    fn check_constraints() {
        let node1max = HEADER + 8 + 2 + 4 + BTREE_MAX_KEY_SIZE + BTREE_MAX_VAL_SIZE;
        assert!(node1max <= BTREE_PAGE_SIZE)
    }

    #[test]
    fn create_node_and_mutate_headers() {
        let mut node = BNode::new(BNodeType::Node, 4);

        let btype = node.btype();
        assert!(matches!(btype, Ok(BNodeType::Node)));

        let keys = node.nkeys();
        assert_eq!(keys, 4);

        node.set_header(BNodeType::Leaf, 6);

        let btype = node.btype();
        assert!(matches!(btype, Ok(BNodeType::Leaf)));

        let keys = node.nkeys();
        assert_eq!(keys, 6);
    }

    #[test]
    fn create_node_with_value() {
        let mut node = BNode::new(BNodeType::Node, 1);
        let val:u64 = 123456789;
        let res = node.set_ptr(0, val);

        assert!(res.is_ok());
        
        let retreived_val = node.get_ptr(0);

        assert!(retreived_val.is_ok());
        assert!(matches!(retreived_val, Ok(123456789)));
    }

    #[test]
    fn create_node_with_values() {
        let mut node = BNode::new(BNodeType::Node, 5);
        _ = node.set_ptr(1, 11111);
        _ = node.set_ptr(0, 22222);
        _ = node.set_ptr(2, 33333);
        _ = node.set_ptr(4, 55555);
        
        let val0 = node.get_ptr(0).expect("Failed to get idx 0");
        let val1 = node.get_ptr(1).expect("Failed to get idx 1");
        let val2 = node.get_ptr(2).expect("Failed to get idx 2");
        let val4 = node.get_ptr(4).expect("Failed to get idx 4");

        assert_eq!(val0, 22222);
        assert_eq!(val1, 11111);
        assert_eq!(val2, 33333);
        assert_eq!(val4, 55555);
    }

    #[test]
    fn create_node_with_offsets() {
        let mut node = BNode::new(BNodeType::Node, 5);

        let _ = node.set_offset(3, 1);
        let _ = node.set_offset(4, 2);
        let set_0 = node.set_offset(0, 3);
        
        let off3 = node.get_offset(3).expect("Failed to get offset 3");
        let off4 = node.get_offset(4).expect("Failed to get offset 4");
        let off0 = node.get_offset(0).expect("Failed to get offset 0");

        assert!(!set_0.is_ok());
        assert_eq!(off3, 1);
        assert_eq!(off4, 2);
        assert_eq!(off0, 0);
    }
}
