enum BNodeType {
    Node(usize),
    Leaf(usize),
}

impl BNodeType {
    fn header(&self) -> i32 {
        match *self {
            BNodeType::Node(_) => 1,
            BNodeType::Leaf(_) => 2,
        }
    }
}

fn main() {
    unimplemented!();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn headers_stay_the_same() {
        let node = BNodeType::Node(1);
        let leaf = BNodeType::Leaf(1);
        assert_eq!(node.header(), 1);
        assert_eq!(leaf.header(), 2);
    }
}
