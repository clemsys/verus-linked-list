pub mod linked_list;

use linked_list::*;
use vstd::prelude::*;

verus! {
    fn main() {
        let mut list = LinkedList::new();
        list.push(1);
        list.push(2);
        list.push(3);
        list.push(4);
        list.push(5);

        for _ in list {
        }
    }
}
