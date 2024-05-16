use vstd::prelude::*;

verus! {
    #[derive(Debug, Clone)]
    pub struct Node<T> {
        pub head: T,
        pub tail: Option<Box<Node<T>>>,
    }

    impl<T> View for Node<T> {
        type V = Seq<T>;

        spec fn view(&self) -> Seq<T>;
    }

    impl<T: DeepView> DeepView for Node<T> {
        type V = Seq<T::V>;

        open spec fn deep_view(&self) -> Seq<T::V> {
            Seq::new(self.view().len(), |i: int| self[i].deep_view())
        }
    }

    impl<T> Node<T> {
        pub open spec fn spec_len(&self) -> nat {
            self.view().len()
        }

        pub open spec fn spec_index(&self, i: int) -> T {
            self.view().index(i)
        }

        pub open spec fn valid(&self) -> bool
            decreases self@.len()
        {
            &&& self@ =~= Seq::new(self@.len() as nat, |i: int| self[i])
            &&& self[0] == self.head
            &&& match self.tail {
                Some(node) => self@.len() == node@.len() + 1 && node@ =~= self@.subrange(1, self@.len() as int) && node.valid(),
                None => self@.len() == 1,
            }
        }

        pub proof fn length_content_equivalence(&self)
            requires
                self.valid(),
            ensures
                self@.len() == 1 <==> self.tail.is_none(),
                self@.len() > 1 <==> self.tail.is_some(),
        {
            assert(self.tail.is_none() ==> self@.len() == 1);
            assert(self.tail.is_some() ==> self@.len() > 1) by {
                assert(self.tail matches Some(node) ==> node@.len() > 0) by {
                    assert(self.tail matches Some(node) ==> node.valid());
                };
            };
        }

        pub open spec fn spec_new(&self, value: T) -> bool {
            self@ =~= Seq::new(1, |i| value)
        }

        pub fn new(value: T) -> (result: Self)
            ensures
                result.valid(),
                result@.len() == 1,
                result.spec_new(value),
        {
            let node = Self {
                head: value,
                tail: None,
            };
            assume(node.spec_new(value));  // axiom
            node
        }

        pub open spec fn spec_push(&self, node: &Node<T>, value: T) -> bool {
            self@ =~= Seq::new((node@.len() + 1) as nat, |i: int| if i == 0 { value } else { node[i - 1] })
        }

        pub fn push(self, value: T) -> (result: Self)
            requires
                self.valid(),
                self@.len() < usize::MAX,
            ensures
                result.valid(),
                result@[0] == value,
                forall|i: int| 0 <= i < self@.len() ==> result@[i + 1] == self@[i],
                result@.len() == self@.len() + 1,
        {
            let new_node = Node {
                head: value,
                tail: Some(Box::new(self)),
            };
            assume(new_node.spec_push(&self, value));  // axiom
            new_node
        }

        pub fn pop(self) -> (result: (T, Option<Self>))
            requires
                self.valid(),
                self@.len() > 0,
            ensures
                result.0 == self@[0],
                self@.len() == 1 <==> result.1.is_none(),
                self@.len() > 1 <==> result.1.is_some(),
                result.1 matches Some(node) ==> {
                    &&& node.valid()
                    &&& node@.len() == self@.len() - 1
                    &&& forall|i: int| 0 <= i < node@.len() ==> node@[i] == self@[i + 1]
                }
        {
            proof {
                self.length_content_equivalence()
            }
            let popped = self.head;
            let tail = match self.tail {
                Some(node) => Some(*node),
                None => None,
            };
            (popped, tail)
        }

        pub fn next(&self) -> (result: Option<&Node<T>>)
            requires
                self.valid(),
            ensures
                self@.len() > 1 <==> result.is_some(),
                self@.len() == 1 <==> result.is_none(),
                result matches Some(node) ==> node.valid(),
        {
            proof {
                self.length_content_equivalence()
            }
            let result: Option<&Node<T>> = if self.tail.is_some() {
                Some(self.tail.as_ref().unwrap())
            } else {
                None
            };
            result
        }
    }


    impl<T> std::ops::Index<usize> for Node<T> {
        type Output = T;

        fn index(&self, index: usize) -> (result: &T)
            requires
                self.valid(),
                index < self@.len(),
            ensures
                result == self@[index as int],
        {
            let mut current = self;
            for i in 0..index
                invariant
                    index < self@.len(),
                    current.valid(),
                    current@.len() == self@.len() - i,
                    current@[(index - i) as int] == self@[index as int],
            {
                current = current.tail.as_ref().unwrap();
            }
            &current.head
        }
    }
}
