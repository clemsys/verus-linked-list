use vstd::prelude::*;

verus! {
    #[verifier(external_fn_specification)]
    pub fn ex_box_new<T>(value: T) -> Box<T> {
        Box::new(value)
    }

    #[derive(Debug, Clone)]
    pub struct Node<T> {
        pub head: T,
        pub tail: Option<Box<Node<T>>>,
        pub ghost length: u64,
    }

    #[derive(Debug, Clone)]
    pub struct LinkedList<T> {
        pub content: Option<Node<T>>,
        pub ghost length: u64,
    }

    impl<T> Node<T> {
        pub open spec fn valid_inner_lengths(&self) -> bool
            decreases self.length
        {
            match self.tail {
                Some(node) => node.length == self.length - 1 && node.valid_inner_lengths(),
                None => self.length == 1,
            }
        }

        pub fn new(value: T) -> (result: Self)
            ensures result.valid_inner_lengths(),
                result.length == 1
        {
            Self {
                head: value,
                tail: None,
                length: 1,
            }
        }

        pub fn push(self, value: T) -> (result: Self)
            requires self.valid_inner_lengths(),
                self.length < u64::MAX,
            ensures result.valid_inner_lengths(),
                result.length == self.length + 1
        {
            Node {
                head: value,
                length: self.length + 1,
                tail: Some(Box::new(self)),
            }
        }
    }

    impl<T> Default for LinkedList<T> {
        fn default() -> Self {
            Self::new()
        }
    }

    impl<T> LinkedList<T> {
        pub open spec fn valid_lengths(&self) -> bool {
            match self.content {
                Some(node) => self.length == node.length && node.valid_inner_lengths(),
                None => self.length == 0,
            }
        }

        pub fn new() -> (result: Self)
            ensures result.valid_lengths(),
                result.length == 0
        {
            Self {
                content: None,
                length: 0,
            }
        }

        pub fn push(&mut self, value: T)
            requires old(self).valid_lengths(),
                old(self).length < u64::MAX,
            ensures self.valid_lengths(),
                self.length == old(self).length + 1
        {
            let new_node = match self.content.take() {
                Some(node) => node.push(value),
                None => {
                    Node::new(value)
                },
            };
            self.length = new_node.length;
            self.content = Some(new_node);
        }

        pub fn pop(&mut self) -> (result: Option<T>)
            requires old(self).valid_lengths(),
            ensures self.valid_lengths(),
                old(self).length > 0 ==> self.length == old(self).length - 1,
                old(self).length == 0 ==> self.length == 0
        {
            match self.content.take() {
                Some(node) => {
                    match node.tail {
                        Some(tail) => self.content = Some(*tail),
                        None => self.content = None,
                    }
                    self.length = self.length - 1;
                    Some(node.head)
                }
                None => None,
            }
        }
    }

    impl<T> Iterator for LinkedList<T> {
        type Item = T;

        fn next(&mut self) -> (result: Option<Self::Item>)
            requires old(self).valid_lengths(),
            ensures self.valid_lengths(),
                old(self).length > 0 ==> self.length == old(self).length - 1,
                old(self).length == 0 ==> self.length == 0
        {
            self.pop()
        }
    }

    pub struct LinkedListGhostIterator<T> {
        pub content: Option<Node<T>>,
        pub length: int,
    }

    impl<T> LinkedListGhostIterator<T> {
        pub open spec fn valid_lengths(&self) -> bool {
            match self.content {
                Some(node) => self.length == node.length as int && node.valid_inner_lengths(),
                None => self.length == 0,
            }
        }
    }

    impl<T> vstd::pervasive::ForLoopGhostIteratorNew for LinkedList<T> {
        type GhostIter = LinkedListGhostIterator<T>;

        open spec fn ghost_iter(&self) -> LinkedListGhostIterator<T> {
            LinkedListGhostIterator {
                content: self.content,
                length: self.length as int,
            }
        }
    }

    impl<T> vstd::pervasive::ForLoopGhostIterator for LinkedListGhostIterator<T> {
        type ExecIter = LinkedList<T>;
        type Item = T;
        type Decrease = int;

        open spec fn exec_invariant(&self, exec_iter: &LinkedList<T>) -> bool {
            //&&& self.content == exec_iter.content
            //&&& self.length == exec_iter.length as int
            //&&& self.valid_lengths()
            &&& exec_iter.valid_lengths()
        }

        open spec fn ghost_invariant(&self, init: Option<&Self>) -> bool {
            true
        }

        open spec fn ghost_ensures(&self) -> bool {
            true //self.content.is_none()
        }

        open spec fn ghost_decrease(&self) -> Option<int> {
            Some(self.length)
        }

        open spec fn ghost_peek_next(&self) -> Option<T> {
            match &self.content {
                Some(node) => Some(node.head),
                None => None,
            }
        }

        open spec fn ghost_advance(&self, _exec_iter: &LinkedList<T>) -> LinkedListGhostIterator<T> {
            LinkedListGhostIterator {
                content: match self.content.unwrap().tail {
                    Some(tail) => Some(*tail),
                    None => None,
                },
                length: self.length - 1,
            }
        }
    }
}
