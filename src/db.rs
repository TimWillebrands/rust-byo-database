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

    /// Retrieves a 64-bit pointer from a node at a specified index.
    ///
    /// # Arguments
    /// * `idx` - Index at which to retrieve the pointer.
    ///
    /// # Returns
    /// * `Ok(u64)` - The pointer if successfully retrieved.
    /// * `Err(String)` - Error message if the index is out of bounds or data extraction fails.
    ///
    /// # Errors
    /// Errors occur if `idx` is out of bounds or if the data slice for the pointer is incorrectly sized.
    ///
    /// # Example
    /// ```
    /// use byodb_rust::db::*;
    /// let node = BNode::new(BNodeType::Leaf, 1); // Assuming initialization is done elsewhere
    /// match node.get_ptr(1) {
    ///     Ok(ptr) => println!("Found pointer: {}", ptr),
    ///     Err(e) => eprintln!("Error: {}", e),
    /// }
    /// ```
    ///
    /// This method is used to access child node pointers in B-trees.
    pub fn get_ptr(&self, idx: u16) -> Result<u64, String> {
        if idx >= self.nkeys() {
            return Err(format!(
                "[get_ptr] Index out of bounds: {} >= keys {}",
                idx,
                self.nkeys()
            ));
        }
        let pos = usize::from((HEADER as u16) + 8 * idx);

        if pos + 8 > self.data.len() {
            return Err(format!(
                "[get_ptr] Index out of data range: position {} + 8 exceeds data length {}",
                pos,
                self.data.len()
            ));
        }

        // Safely extract a u64 from the data slice
        let ptr_bytes = &self.data[pos..pos + 8].try_into().map_err(|_| {
            format!(
                "Failed to extract a u64 from data slice: expected 8 bytes, found {}",
                self.data[pos..].len()
            )
        })?;
        let ptr = u64::from_le_bytes(*ptr_bytes);

        Ok(ptr)
    }

    pub fn set_ptr(&mut self, idx: u16, val: u64) -> Result<(), String> {
        if idx >= self.nkeys() {
            return Err(format!(
                "[set_ptr] Index out of bounds: {} >= keys: {}",
                idx,
                self.nkeys()
            ));
        }
        let pos = usize::from((HEADER as u16) + 8 * idx);

        let mut val_bytes = val.to_le_bytes();
        let slice = &mut self.data[pos..pos + 8];

        slice.swap_with_slice(&mut val_bytes);

        Ok(())
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
        if idx > self.nkeys() {
            return Err(format!(
                "[get_offset] Index '{}' is out of bounds. There are only '{} keys'",
                idx,
                self.nkeys()
            ));
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
            return Err(format!(
                "[get_val] Index out of bounds: {} >= nkeys: {}",
                idx,
                self.nkeys()
            ));
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

    /// Performs a lookup to find the position of a child node whose key range intersects with the given key.
    ///
    /// This method scans through the keys of the node starting from index 1, assuming the first key (index 0)
    /// is always less than or equal to any given key. It identifies the highest index at which the node's key
    /// is less than or equal to the provided key. This index represents the closest child node whose range
    /// could contain or is related to the given key.
    ///
    /// Note: This function returns an index that may not directly correspond to the exact key if it doesn't exist.
    /// It's essential to verify the presence of the key at the returned index in the node if exact matches are required.
    ///
    /// # Arguments
    /// * `key` - The key for which the lookup is performed, as a byte slice.
    ///
    /// # Returns
    /// * `Result<u16, String>` - Ok contains the index of the closest child node by key range.
    ///   Err returns a string describing the error if any issues occur during key retrieval.
    pub fn lookup_le(&self, key: &[u8]) -> Result<u16, String> {
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

    /// Performs an exact key lookup in the node, including the first key in the search.
    ///
    /// This method extends `lookup_le` by explicitly checking the first key for a match
    /// before proceeding with the lookup, ensuring that the search covers all keys in the node.
    ///
    /// Refer to `lookup_le` for details on the lookup process starting from index 1.
    ///
    /// # Arguments
    /// * `key` - The key to search for, as a byte slice.
    ///
    /// # Returns
    /// * `Result<u16, String>` - Ok contains the index of the key if found, including index 0.
    ///   Err returns a string describing the error if any issues occur during key retrieval.
    ///
    /// This method is particularly useful for operations requiring the exact position of a key,
    /// complementing `lookup_le` which is optimized for navigating child nodes based on key ranges.
    pub fn exact_key_lookup(&self, key: &[u8]) -> Result<u16, String> {
        // Directly compare the first key if there is one
        if self.nkeys() > 0 {
            let first_key = self.get_key(0)?;
            if first_key == key {
                return Ok(0);
            }
        }

        // Use lookup_le for subsequent keys
        self.lookup_le(key)
    }

    fn enlarge(&mut self, required_space: usize) -> Result<(), String> {
        let extra_space = std::cmp::max(self.data.capacity() / 10, 256); // Example: 10% or at least 256 bytes
        self.data.resize(required_space + extra_space, 0); // Adjust length, filling new space with 0s

        println!(
            "Resized space in the node data. Required: {}, New-available: {}",
            required_space,
            self.data.capacity()
        );
        Ok(())
    }

    /// Appends a key-value pair into a specified position within a BNode.
    ///
    /// Sets a pointer at the given index, copies the key and value into the node's data,
    /// and updates the offset for the next key-value pair, all without external crate dependencies.
    ///
    /// # Arguments
    ///
    /// * `idx` - The index at which to append the key-value pair.
    /// * `ptr` - The pointer associated with the key-value pair (not used in this example, but typically for linking nodes).
    /// * `key` - The key to append.
    /// * `val` - The value associated with the key.
    ///
    /// # Returns
    ///
    /// Result<(), String> indicating success or failure.
    ///
    /// The method is useful for navigating B-trees, where finding the correct child node based on key ranges
    /// is essential for insertions, deletions, and searches.
    pub fn append_kv(
        &mut self,
        idx: u16,
        ptr: u64,
        key: &[u8],
        val: &[u8],
    ) -> Result<(), String> {
        // ptrs
        self.set_ptr(idx, ptr)?;

        // Calculate the position for the KV pair data
        let pos = self.kv_pos(idx)? as usize;

        // Calculate the additional space needed for the new KV pair.
        // 2B for each length + key and value sizes
        let additional_space = 4 + key.len() + val.len();

        // Ensure there is enough space in the data vector
        let required_space = pos + additional_space;

        if required_space > self.data.len() {
            self.enlarge(required_space)?;
        }

        // Write the length of the key in little-endian format
        let key_len_bytes = (key.len() as u16).to_le_bytes();
        self.data[pos..pos + 2].copy_from_slice(&key_len_bytes);

        // Write the length of the value in little-endian format
        let val_len_bytes = (val.len() as u16).to_le_bytes();
        self.data[pos + 2..pos + 4].copy_from_slice(&val_len_bytes);

        // Copy the key bytes
        self.data[pos + 4..pos + 4 + key.len()].copy_from_slice(key);

        // Copy the value bytes
        self.data[pos + 4 + key.len()..pos + 4 + key.len() + val.len()].copy_from_slice(val);

        // Update the offset for the next key-value pair
        let next_kv_offset = (pos + 4 + key.len() + val.len()) as u16;

        self.set_offset(idx + 1, next_kv_offset)
    }

    /// The nodeAppendRange function copies keys from an old node to a new node.
    /// copy multiple KVs into the position
    pub fn append_range(
        &mut self,
        old: &BNode,
        dst_new: u16,
        src_old: u16,
        n: u16,
    ) -> Result<(), String> {
        if src_old + n > old.nkeys() {
            return Err(format!(
                "src_old + n exceeds the number of keys in the old node. src_old: {}, n: {}, old.nkeys(): {}",
                src_old, n, old.nkeys()
            ));
        }
        if dst_new + n > self.nkeys() {
            return Err(format!(
                "dst_new + n exceeds the number of keys in the new node. dst_new: {}, n: {}, self.nkeys(): {}",
                dst_new, n, self.nkeys()
            ));
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

        // Correctly calculating additional space required for the KV pairs.
        let additional_space = src_slice.len();

        // Calculate the required space in the destination node. This should be
        // where the copied data ends. This accounts for the length of existing
        // data up to `dst_start` plus the length of the data being copied.
        let required_space = dst_start + additional_space;

        // Ensure there is enough space in the destination node's data vector.
        if required_space > self.data.len() {
            self.enlarge(required_space)?;
        }

        let dst_slice = &mut self.data[dst_start..dst_start + src_slice.len()];
        dst_slice.copy_from_slice(src_slice);

        Ok(())
    }

    /// Creates a new BNode by inserting a new key-value pair into the current node.
    ///
    /// The new node is a modified copy of the current node (`self`) with the new key-value pair
    /// inserted at the specified index. This method is intended for leaf nodes in a B-tree and
    /// ensures the logical structure of the tree is maintained.
    ///
    /// # Arguments
    ///
    /// * `idx` - The index at which the new key-value pair should be inserted.
    /// * `key` - The key to insert.
    /// * `val` - The value associated with the key.
    ///
    /// # Returns
    ///
    /// A new `BNode` instance representing the current node with the additional key-value pair,
    /// or an error if the operation cannot be completed.
    pub fn leaf_insert(&self, idx: u16, key: &[u8], val: &[u8]) -> Result<BNode, String> {
        let mut new = BNode::new(BNodeType::Leaf, self.nkeys() + 1);

        // Copy all key-value pairs from `self` to `new` up to the one being inserted
        new.append_range(self, 0, 0, idx)?;
        new.append_kv(idx, 0, key, val)?;
        new.append_range(self, idx + 1, idx, self.nkeys() - idx)?;

        Ok(new)
    }

    pub fn leaf_update(&self, idx: u16, key: &[u8], val: &[u8]) -> Result<BNode, String> {
        let mut new = BNode::new(BNodeType::Leaf, self.nkeys());

        println!("src: {:?}", self.data);
        println!("new: {:?}", new.data);
        // Copy all key-value pairs from `self` to `new` up to the one being updated
        new.append_range(self, 0, 0, idx)?;

        println!("newer: {:?}", new.data);
        // Insert key-value at the spot that was to be "updated"
        new.append_kv(idx, 0, key, val)?;

        // Copy the remaining key-value pairs from `self` to `new` after the updated one
        new.append_range(self, idx + 1, idx + 1, self.nkeys() - idx - 1)?;

        Ok(new)
    }

    pub fn get_kvs(&self, from_idx: u16, mut amount: u16) -> Result<Vec<(&[u8], &[u8])>, String> {
        // Cap the amount to the maximum available keys from from_idx
        if from_idx >= self.nkeys() {
            return Ok(Vec::new()); // Return an empty vector if from_idx is out of bounds
        }

        if from_idx + amount > self.nkeys() {
            amount = self.nkeys() - from_idx; // Adjust amount to not exceed available keys
        }

        let mut kvs = Vec::new();

        for i in from_idx..from_idx + amount {
            let key = self
                .get_key(i)
                .map_err(|e| format!("Failed to get key at index {}: {}", i, e))?;

            let val = self
                .get_val(i)
                .map_err(|e| format!("Failed to get value at index {}: {}", i, e))?;

            kvs.push((key, val));
        }

        Ok(kvs)
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
        // where to insert the key?
        let idx = node.lookup_le(key)?;

        // act depending on the node type
        match node.btype()? {
            BNodeType::Leaf => match key.cmp(node.get_key(idx)?) {
                std::cmp::Ordering::Equal => node.leaf_update(idx, key, val),
                _ => node.leaf_insert(idx, key, val),
            },
            BNodeType::Node => self.insert(&node, idx, key, val),
        }
    }

    // part of the treeInsert(): KV insertion to an internal node
    pub fn insert(
        &mut self,
        node: &BNode,
        idx: u16,
        key: &[u8],
        val: &[u8],
    ) -> Result<BNode, String> {
        assert!(false, "We stopped at: https://build-your-own.org/database/04_btree_code_1 4.4 Step 4: Handle Internal Nodes");
        let mut new = BNode {
            data: vec![0; 2 * BTREE_PAGE_SIZE as usize],
        };
        Ok(new)
    }
}

#[cfg(test)]
mod node {
    use super::*;

    macro_rules! assert_eq_as_str {
        ($left:expr, $right:expr) => {{
            let left_str = String::from_utf8_lossy($left);
            let right_str = String::from_utf8_lossy($right);
            assert!(
                left_str == right_str,
                "assertion failed: `(left == right)`\n  left: `{}`\n right: `{}`",
                left_str,
                right_str
            );
        }};
    }

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
    fn create_and_mutate_headers() {
        let mut node = BNode::new(BNodeType::Node, 4);
        let required_size = usize::from((HEADER as u16) + 8 * 4 + 2 * 4);

        assert_eq!(node.data.len(), required_size);

        let btype = node.btype();
        assert!(matches!(btype, Ok(BNodeType::Node)));

        let keys = node.nkeys();
        assert_eq!(keys, 4);

        node.set_header(BNodeType::Leaf, 6);

        let btype = node.btype();
        assert!(matches!(btype, Ok(BNodeType::Leaf)));

        let keys = node.nkeys();
        assert_eq!(keys, 6);

        let required_size = usize::from((HEADER as u16) + 8 * 6 + 2 * 6);
        assert_eq!(node.data.len(), required_size);
    }

    #[test]
    fn create_with_ptrvalue() {
        let mut node = BNode::new(BNodeType::Node, 1);
        let val: u64 = 123456789;
        let res = node.set_ptr(0, val);

        assert!(res.is_ok());

        let retreived_val = node.get_ptr(0);

        assert!(retreived_val.is_ok());
        assert!(matches!(retreived_val, Ok(123456789)));
    }

    #[test]
    fn check_ptrvalues() {
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
    fn lookup_key_values() -> Result<(), String> {
        let node = BNode::new(BNodeType::Node, 0)
            .leaf_insert(0, b"hallo", b"wereld")?
            .leaf_insert(1, b"hello", b"world")?;

        let pos = node.exact_key_lookup(b"hallo")?;
        let val = node.get_val(pos);
        let key = node.get_key(pos);
        assert_eq!(pos, 0);
        assert_eq!(val, Ok(b"wereld" as &[u8]));
        assert_eq!(key, Ok(b"hallo" as &[u8]));

        let pos = node.exact_key_lookup(b"hello")?;
        let val = node.get_val(pos);
        let key = node.get_key(pos);
        assert_eq!(pos, 1);
        assert_eq!(val, Ok(b"world" as &[u8]));
        assert_eq!(key, Ok(b"hello" as &[u8]));

        let pos = node.exact_key_lookup(b"nonsense")?;
        let key = node.get_key(pos);
        assert_ne!(key, Ok(b"nonsense" as &[u8]));

        Ok(())
    }

    #[test]
    fn insert_key_values() -> Result<(), String> {
        let node = BNode::new(BNodeType::Node, 0);

        let new = node.leaf_insert(0, b"hallo", b"wereld")?;
        let pos = new.exact_key_lookup(b"hallo")?;
        assert_eq!(pos, 0);
        let val = new.get_val(pos);
        assert_eq!(val, Ok(b"wereld" as &[u8]));

        let new = new.leaf_insert(1, b"hello", b"world")?;
        let pos = new.exact_key_lookup(b"hallo")?;
        assert_eq!(pos, 0);
        assert_eq!(new.get_val(pos), Ok(b"wereld" as &[u8]));
        let pos = new.exact_key_lookup(b"hello")?;
        assert_eq!(pos, 1);
        assert_eq!(new.get_val(pos), Ok(b"world" as &[u8]));

        let new = new.leaf_insert(0, b"bienvenue", b"monde")?;
        let pos = new.exact_key_lookup(b"bienvenue")?;
        assert_eq!(pos, 0);
        assert_eq!(new.get_val(pos), Ok(b"monde" as &[u8]));
        let pos = new.exact_key_lookup(b"hallo")?;
        assert_eq!(new.get_val(pos), Ok(b"wereld" as &[u8]));
        assert_eq!(pos, 1);
        let pos = new.exact_key_lookup(b"hello")?;
        assert_eq!(pos, 2);
        assert_eq!(new.get_val(pos), Ok(b"world" as &[u8]));

        Ok(())
    }

    #[test]
    fn update_key_values() -> Result<(), String> {
        let node = BNode::new(BNodeType::Node, 0);

        let new = node.leaf_insert(0, b"hallo", b"wereld")?;
        let pos = new.exact_key_lookup(b"hallo")?;
        let val = new.get_val(pos);
        assert_eq!(pos, 0);
        assert_eq!(val, Ok(b"wereld" as &[u8]));

        let new = new.leaf_update(0, b"hello", b"world")?;

        let pos = new.exact_key_lookup(b"hallo")?;
        let key = new.get_key(pos);
        assert_ne!(key, Ok(b"hallo" as &[u8]));

        let pos = new.exact_key_lookup(b"hello")?;
        let val = new.get_val(pos);
        assert_eq!(pos, 0);
        assert_eq!(val, Ok(b"world" as &[u8]));

        Ok(())
    }

    #[test]
    fn test_leaf_insert_and_update() -> Result<(), String> {
        // Initial insertions in non-sequential order
        let mut node = BNode::new(BNodeType::Leaf, 0)
            .leaf_insert(0, b"world", b"earth")? // Insert "world" at position 0
            .leaf_insert(0, b"hello", b"world")? // Insert "hello" at position 0, shifting "world"
            .leaf_insert(1, b"hallo", b"wereld")?; // Insert "hallo" at position 1, between "hello" and "world"

        let kvs = node.get_kvs(0, 3)?;
        for (i, (key, val)) in kvs.iter().enumerate() {
            let key_str = String::from_utf8_lossy(key);
            let val_str = String::from_utf8_lossy(val);
            println!("Key at index {}: {} => Value: {}", i, key_str, val_str);
        }

        let le = node.exact_key_lookup(b"hello")?;
        let key = node.get_key(le)?;
        let val = node.get_val(le)?;
        let key_str = String::from_utf8_lossy(key);
        let val_str = String::from_utf8_lossy(val);
        println!("Lookup at index {}: {} => Value: {}", le, key_str, val_str);

        // Verify initial insertions
        assert_eq_as_str!(
            node.get_val(node.exact_key_lookup(b"hello")?).unwrap(),
            b"world"
        );
        assert_eq_as_str!(
            node.get_val(node.exact_key_lookup(b"hallo")?).unwrap(),
            b"wereld"
        );
        assert_eq_as_str!(
            node.get_val(node.exact_key_lookup(b"world")?).unwrap(),
            b"earth"
        );

        node = node.leaf_update(node.exact_key_lookup(b"world")?, b"world", b"planet")?;

        // Verify update
        assert_eq_as_str!(
            node.get_val(node.exact_key_lookup(b"world")?).unwrap(),
            b"planet"
        );

        // Verify other keys are unaffected
        assert_eq_as_str!(
            node.get_val(node.exact_key_lookup(b"hello")?).unwrap(),
            b"world"
        );
        assert_eq_as_str!(
            node.get_val(node.exact_key_lookup(b"hallo")?).unwrap(),
            b"wereld"
        );

        // Attempt to lookup a key that doesn't exist
        let pos = node.exact_key_lookup(b"unknown")?;
        assert_ne!(node.get_key(pos).unwrap(), b"unknown");

        // Verify behavior at the boundaries of the keys
        // Looking up a key smaller than any existing key
        let smallest_pos = node.exact_key_lookup(b"a")?;
        assert_eq!(smallest_pos, 0); // Should point to the first key as the smallest key

        // Looking up a key larger than any existing key
        let largest_pos = node.exact_key_lookup(b"z")?;
        assert_eq!(largest_pos, node.nkeys() - 1); // Should point to the last key as the largest key

        Ok(())
    }
}
