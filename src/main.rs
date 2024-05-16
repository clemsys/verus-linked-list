pub mod linked_list;
pub mod node;

use linked_list::*;
use vstd::prelude::*;

verus! {
    fn main() {
        // example usage
        let mut list = LinkedList::new();

        list.push(0);
        list.push(1);
        list.push(2);
        list.push(3);
        list.push(4);
        assert(list@[4] == 0);
        list.push(5);

        let popped = list.pop();
        assert(popped matches Some(i) && i == 5);
        let popped = list.pop();
        let popped = list.pop();
        let popped = list.pop();
        assert(popped matches Some(i) && i == 2);
        let popped = list.pop();
        let popped = list.pop();
        assert(popped matches Some(i) && i == 0);
        let popped = list.pop();
        assert(popped matches None)
    }
}
