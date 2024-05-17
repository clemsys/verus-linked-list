use crate::linked_list::LinkedList;
use vstd::prelude::*;

verus! {
    impl<T> Iterator for LinkedList<T> {
        type Item = T;

        fn next(&mut self) -> (popped: Option<Self::Item>)
            requires
                old(self).valid(),
            ensures
                self.valid(),
                old(self).0 matches Some(node) ==> {
                    &&& self@.len() == old(self)@.len() - 1
                    &&& popped matches Some(value)
                    &&& value == old(self)@[0]
                    &&& forall|i: int| 0 <= i < self@.len() ==> self@[i] == old(self)@[i + 1]
                },
                old(self).0.is_none() ==> {
                    &&& self@.len() == 0
                    &&& popped.is_none()
                }
        {
            self.pop()
        }
    }

    pub struct LinkedListGhostIterator<T>(pub LinkedList<T>);

    impl<T> vstd::pervasive::ForLoopGhostIteratorNew for LinkedList<T> {
        type GhostIter = LinkedListGhostIterator<T>;

        open spec fn ghost_iter(&self) -> LinkedListGhostIterator<T> {
            LinkedListGhostIterator(*self)
        }
    }

    impl<T> vstd::pervasive::ForLoopGhostIterator for LinkedListGhostIterator<T> {
        type ExecIter = LinkedList<T>;

        type Item = T;

        type Decrease = nat;

        open spec fn exec_invariant(&self, exec_iter: &LinkedList<T>) -> bool {
            &&& exec_iter.valid()
            &&& self.0.valid()
            &&& self.0@ =~= exec_iter@
        }

        open spec fn ghost_invariant(&self, init: Option<&Self>) -> bool {
            true
        }

        open spec fn ghost_ensures(&self) -> bool {
            self.0.0.is_none()
        }

        open spec fn ghost_decrease(&self) -> Option<nat> {
            Some(self.0@.len())
        }

        open spec fn ghost_peek_next(&self) -> Option<T> {
            match self.0.0 {
                Some(node) => Some(node.head),
                None => None,
            }
        }

        open spec fn ghost_advance(&self, _exec_iter: &LinkedList<T>) -> LinkedListGhostIterator<T> {
            LinkedListGhostIterator(
                LinkedList(
                    match self.0.0 {
                        None => None,
                        Some(node) => match node.tail {
                            Some(tail) => Some(*tail),
                            None => None,
                        }
                    }
                )
            )
        }
    }
}
