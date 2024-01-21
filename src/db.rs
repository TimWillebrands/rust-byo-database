const HEADER:u32 = 4;
const BTREE_PAGE_SIZE:u32 = 4096;
const BTREE_MAX_KEY_SIZE:u32 = 1000;
const BTREE_MAX_VAL_SIZE:u32 = 3000;

pub enum BNodeType {
    Node,
    Leaf,
}

impl BNodeType {
    pub fn header(&self) -> u8 {
        match *self {
            BNodeType::Node => 1,
            BNodeType::Leaf => 2,
        }
    }
}
pub struct BNode {
    data: [u8; 5]// can be dumped to the disk
}

pub struct BTree {
    // pointer (a nonzero page number)
    root: u64, 
    // callbacks for managing on-disk pages
    // get func(uint64) BNode // dereference a pointer
    // new func(BNode) uint64 // allocate a new page
    // del func(uint64)       // deallocate a page
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn headers_stay_the_same() {
        let node = BNodeType::Node;
        let leaf = BNodeType::Leaf;
        assert_eq!(node.header(), 1);
        assert_eq!(leaf.header(), 2);
    }

    #[test]
    fn check_constraints() {
        let node1max = HEADER + 8 + 2 + 4 + BTREE_MAX_KEY_SIZE + BTREE_MAX_VAL_SIZE;
        assert!(node1max <= BTREE_PAGE_SIZE)
    }
}
