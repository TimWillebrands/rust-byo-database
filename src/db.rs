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

impl BNode {
    pub fn new(typ: BNodeType, keys: u16) -> BNode {
        let [type_high, type_low] = typ.as_u16().to_le_bytes();
        let [keys_high, keys_low] = keys.to_le_bytes();

        let required_size = usize::from((HEADER as u16) + 8 * keys + 2 * keys);
        let mut data = vec![type_high, type_low, keys_high, keys_low];
        data.resize(required_size.into(), 0);

        BNode { data }
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
        let required_size = usize::from((HEADER as u16) + 8 * keys + 2 * keys);
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

    pub fn set_ptr(&mut self, idx: u16, val: u64) -> Result<(), String> {
        if idx >= self.nkeys() {
            return Err("Index out of bounds".to_string());
        }
        let pos = usize::from((HEADER as u16) + 8 * idx);

        let mut val_bytes = val.to_le_bytes();
        let slice = &mut self.data[pos..pos + 8];

        slice.swap_with_slice(&mut val_bytes);

        return Ok(());
    }

    fn offset(&self, idx: u16) -> [u8; 2] {
        let offset = usize::from((HEADER as u16) + 8 * self.nkeys() + 2 * (idx - 1));
        self.data[offset..offset + 2]
            .try_into()
            .expect("Offset was not right size? 2 bytes")
    }

    fn offset_mut(&mut self, idx: u16) -> &mut [u8] {
        let offset = usize::from((HEADER as u16) + 8 * self.nkeys() + 2 * (idx - 1));
        &mut self.data[offset..offset + 2]
    }

    pub fn get_offset(&self, idx: u16) -> Result<u16, String> {
        if idx >= self.nkeys() {
            return Err("Index out of bounds".to_string());
        }

        match idx {
            0 => Ok(0),
            _ => Ok(u16::from_le_bytes(self.offset(idx))),
        }
    }

    pub fn set_offset(&mut self, idx: u16, offset: u16) -> Result<(), String> {
        if idx == 0 {
            return Err("Plz no touching the 0th offset".to_string());
        }

        let off = self.offset_mut(idx);
        let mut val = offset.to_le_bytes();

        off.swap_with_slice(&mut val);

        Ok(())
    }

    pub fn kv_pos(&self, idx: u16) -> Result<u16, String> {
        match self.get_offset(idx) {
            Ok(off) => Ok((HEADER as u16) + 8 * self.nkeys() + 2 * self.nkeys() + off),
            Err(err) => Err(err),
        }
    }

    pub fn get_key(&self, idx: u16) -> Result<&[u8], String> {
        let pos = self.kv_pos(idx)? as usize;

        if pos + 2 > self.data.len() {
            return Err("Not enough data to read key length".to_string());
        }

        let klen_bytes: [u8; 2] = self.data[pos..pos + 2]
            .try_into()
            .map_err(|_| "Failed to read key length".to_string())?;

        let klen = u16::from_le_bytes(klen_bytes) as usize;
        if pos + 4 + klen > self.data.len() {
            return Err("Key length exceeds data bounds".to_string());
        }

        Ok(&self.data[pos + 4..pos + 4 + klen])
    }

    pub fn get_val(&self, idx: u16) -> Result<&[u8], String> {
        if idx >= self.nkeys() {
            return Err("Index out of bounds".to_string());
        }

        let pos = self.kv_pos(idx)? as usize; // Handle error if kv_pos fails

        // Check if there's enough data to read key length and value length
        if pos + 4 > self.data.len() {
            return Err("Not enough data to read key and value length".to_string());
        }

        let klen_bytes: [u8; 2] = self.data[pos..pos + 2]
            .try_into()
            .map_err(|_| "Failed to read key length".to_string())?;

        let vlen_bytes: [u8; 2] = self.data[pos + 2..pos + 4]
            .try_into()
            .map_err(|_| "Failed to read value length".to_string())?;

        let klen = u16::from_le_bytes(klen_bytes) as usize;
        let vlen = u16::from_le_bytes(vlen_bytes) as usize;

        // Ensure the entire key-value pair is within the bounds of the data
        if pos + 4 + klen + vlen > self.data.len() {
            return Err("Key-value pair exceeds data bounds".to_string());
        }

        // Return the value part as a slice
        Ok(&self.data[pos + 4 + klen..pos + 4 + klen + vlen])
    }

    /// determine the size of the node.
    pub fn nbytes(&self) -> Result<u16, String> {
        self.kv_pos(self.nkeys())
    }

    /// To insert a key into a leaf node, we need to look up its position in the sorted KV list.
    /// returns the first kid node whose range intersects the key. (kid[i] <= key)
    /// TODO: Bisect
    pub fn node_lookup_le(&self, key: &[u8]) -> Result<u16, String> {
        let mut last_found = 0u16; // Initialize with 0, assuming the first key is always less than or equal

        // Start from 1 since the first key is always considered less than or equal
        for i in 1..self.nkeys() {
            let current_key = self.get_key(i)?;
            match current_key.cmp(key) {
                std::cmp::Ordering::Greater => break,
                _ => last_found = i,
            }
        }

        Ok(last_found)
    }

    /// The nodeAppendKV function copies a KV pair to the new node.
    pub fn node_append_kv(
        &mut self,
        idx: u16,
        ptr: u64,
        key: &[u8],
        val: &[u8],
    ) -> Result<(), String> {
        // ptrs
        self.set_ptr(idx, ptr)?;

        // KVs
        let pos = self.kv_pos(idx)? as usize;

        let [dlen_high, dlen_low] = (key.len() as u16).to_le_bytes();
        self.data[pos + 0] = dlen_high;
        self.data[pos + 1] = dlen_low;
        self.data[pos + 2] = dlen_high;
        self.data[pos + 3] = dlen_low;

        let end_of_key_pos = pos + 4 + key.len();
        let key_slice = &mut self.data[pos + 4..end_of_key_pos];
        key_slice.copy_from_slice(key);

        let val_slice = &mut self.data[end_of_key_pos..end_of_key_pos + val.len()];
        val_slice.copy_from_slice(val);

        // the offset of the next key
        self.set_offset(
            idx + 1,
            self.get_offset(idx)? + 4 + key.len() as u16 + val.len() as u16,
        )?;

        Ok(())
    }

    /// The nodeAppendRange function copies keys from an old node to a new node.
    /// copy multiple KVs into the position
    pub fn node_append_range(
        &mut self,
        old: &BNode,
        dst_new: u16,
        src_old: u16,
        n: u16,
    ) -> Result<(), String> {
        if src_old + n <= old.nkeys() {
            return Err("src_old has insuffiecient space/keys for this append".to_string());
        }
        if dst_new + n <= self.nkeys() {
            return Err("dst_new has insuffiecient space/keys for this append".to_string());
        }
        if n == 0 {
            return Ok(());
        }

        // pointers
        for i in 0..n {
            self.set_ptr(dst_new + i, old.get_ptr(src_old + i)?)?;
        }

        // offsets
        let dst_begin = self.get_offset(dst_new)?;
        let src_begin = old.get_offset(src_old)?;
        for i in 1..=n {
            let offset = dst_begin + old.get_offset(src_old + i)? - src_begin;
            self.set_offset(dst_new + i, offset)?;
        }

        // KVs
        let begin = old.kv_pos(src_old)? as usize;
        let end = old.kv_pos(src_old + n)? as usize;
        let dst_start = self.kv_pos(dst_new)? as usize;

        let src_slice = &old.data[begin..end];
        let dst_slice = &mut self.data[dst_start..dst_start + src_slice.len()];
        dst_slice.copy_from_slice(src_slice);

        Ok(())
    }

    pub fn leaf_insert(
        &mut self,
        old: &BNode,
        idx: u16,
        key: &[u8],
        val: &[u8],
    ) -> Result<(), String> {
        self.set_header(BNodeType::Leaf, old.nkeys() + 1);
        self.node_append_range(old, 0, 0, idx)?;
        self.node_append_kv(idx, 0, key, val)?;
        self.node_append_range(old, idx + 1, idx, old.nkeys() - idx)?;

        Ok(())
    }

    pub fn leaf_update(
        &mut self,
        old: &BNode,
        idx: u16,
        key: &[u8],
        val: &[u8],
    ) -> Result<(), String> {
        assert!(false, "We stopped at: https://build-your-own.org/database/04_btree_code_1 4.4 Step 3: Recursive Insertion");

        Ok(())
    }
}

pub struct BTree {
    // pointer (a nonzero page number)
    root: u64,
    // callbacks for managing on-disk pages
    // get func(uint64) BNode // dereference a pointer
    // new func(BNode) uint64 // allocate a new page
    // del func(uint64)       // deallocate a page
}

impl BTree {
    /// insert a KV into a node, the result might be split into 2 nodes.
    /// the caller is responsible for deallocating the input node
    /// and splitting and allocating result nodes.
    pub fn tree_insert(&mut self, node: BNode, key: &[u8], val: &[u8]) -> Result<BNode, String> {
        // the result node.
        // it's allowed to be bigger than 1 page and will be split if so
        let mut new = BNode {
            data: vec![0; 2 * BTREE_PAGE_SIZE as usize],
        };

        // where to insert the keu?
        let idx = node.node_lookup_le(key)?;

        // act depending on the node type
        let _ = match node.btype()? {
            BNodeType::Leaf => {
                // leaf, node.getKey(idx) <= key
                match key.cmp(node.get_key(idx)?) {
                    std::cmp::Ordering::Equal => new.leaf_update(&node, idx, key, val),
                    _ => new.leaf_insert(&node, idx, key, val),
                }
            }
            BNodeType::Node => self.node_insert(&new, &node, idx, key, val),
        };

        Ok(new)
    }

    // part of the treeInsert(): KV insertion to an internal node
    pub fn node_insert(&mut self, new: &BNode, node: &BNode, idx: u16, key: &[u8], val: &[u8] ) -> Result<(), String> {

        assert!(false, "We stopped at: https://build-your-own.org/database/04_btree_code_1 4.4 Step 4: Handle Internal Nodes");
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
        let val: u64 = 123456789;
        let res = node.set_ptr(0, val);

        assert!(res.is_ok());

        let retreived_val = node.get_ptr(0);

        assert!(retreived_val.is_ok());
        assert!(matches!(retreived_val, Ok(123456789)));
    }

    #[test]
    fn values() {
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
    fn offsets() {
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

    #[test]
    fn key_values() {
        let mut node = BNode::new(BNodeType::Node, 5);

        // node.node_append_kv(3, 1337, )
        // let _ = node.set_offset(3, 1);
        // let _ = node.set_offset(4, 2);
        // let set_0 = node.set_offset(0, 3);
        //
        // let off3 = node.get_offset(3).expect("Failed to get offset 3");
        // let off4 = node.get_offset(4).expect("Failed to get offset 4");
        // let off0 = node.get_offset(0).expect("Failed to get offset 0");
        //
        // assert!(!set_0.is_ok());
        // assert_eq!(off3, 1);
        // assert_eq!(off4, 2);
        // assert_eq!(off0, 0);
    }
}
