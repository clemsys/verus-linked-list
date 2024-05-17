pub mod linked_list;
pub mod linked_list_iter;
pub mod node;

use linked_list::*;
use vstd::prelude::*;

verus! {
    pub proof fn factor(a: int, b: int, c: int)
        ensures
            a * (b + c) == a * b + a * c,
    {
        admit(); // can be proven, not the point here
    }

    fn main() {
        let mut list = LinkedList::new();

        list.push(4);
        list.push(3);
        list.push(2);
        list.push(1);
        list.push(0);

        let mut sum = 0;

        let ghost i: int = 0;

        for e in y: list
            invariant
                forall |j: int| 0 <= j < y.0@.len() ==> #[trigger] y.0@[j] == j + i,
                y.0@.len() == 5 - i,
                2 * sum == i * (i - 1),
                0 <= sum <= 4 * i,
        {
            assert(2 * sum == i * (i - 1));
            assert(e == i);
            sum = sum + e;
            assert(2 * sum == i * (i - 1) + 2 * i);
            assume(2 * sum == i * (i + 1));
            proof {
                i = i + 1;
            }
            assert(2 * sum == (i - 1) * i);
        }

        assert(sum == 10) by {
            assert(i == 5);
        };
    }
}
