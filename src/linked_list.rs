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
        pub ghost length: usize,
    }

    impl<T> Node<T> {
        pub open spec fn valid(&self) -> bool
            decreases self.length
        {
            &&& self@ =~= Seq::new(self.length as nat, |i: int| self[i])
            &&& self@[0] == self.head
            &&& match self.tail {
                Some(node) => self.length == node.length + 1 && node@ =~= Seq::new((self.length - 1) as nat, |i: int| self[i + 1]) && node.valid(),
                None => self.length == 1,
            }
        }

        pub proof fn length_content_equivalence(&self)
            requires
                self.valid(),
            ensures
                self.length == 1 <==> self.tail.is_none(),
                self.length > 1 <==> self.tail.is_some(),
        {
            assert(self.tail.is_none() ==> self.length == 1);
            assert(self.tail.is_some() ==> self.length > 1) by {
                assert(self.tail.is_some() ==> self.tail->0.length > 0) by {
                    assert(self.tail.is_some() ==> self.tail->0.valid());
                };
            };
        }

        pub open spec fn spec_new(&self, value: T) -> bool {
            self@ =~= Seq::new(1, |i| value)
        }

        pub fn new(value: T) -> (result: Self)
            ensures
                result.valid(),
                result.length == 1,
                result.spec_new(value),
        {
            let node = Self {
                head: value,
                tail: None,
                length: 1,
            };
            assume(node.spec_new(value));
            node
        }

        pub open spec fn spec_push(&self, node: &Node<T>, value: T) -> bool {
            self@ =~= Seq::new((node.length + 1) as nat, |i: int| if i == 0 { value } else { node[i - 1] })
        }

        pub fn push(self, value: T) -> (result: Self)
            requires
                self.valid(),
                self.length < usize::MAX,
            ensures
                result.valid(),
                result.length == self.length + 1,
        {
            let new_node = Node {
                head: value,
                length: self.length + 1,
                tail: Some(Box::new(self)),
            };
            assume(new_node.spec_push(&self, value));
            new_node
        }

        pub open spec fn spec_len(&self) -> nat {
            self.view().len()
        }

        pub open spec fn spec_index(&self, i: int) -> T {
            self.view().index(i)
        }

        pub fn next(&self) -> (result: Option<&Node<T>>)
            requires
                self.valid(),
            ensures
                self.length > 1 <==> result.is_some(),
                self.length == 1 <==> result.is_none(),
                result.is_some() ==> result->0.valid(),
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
                index < self.length,
            ensures
                result == self@[index as int],
        {
            let mut current = self;
            for i in 0..index
                invariant
                    index < self.length,
                    current.valid(),
                    current.length == self.length - i,
                    current@[(index - i) as int] == self@[index as int],
            {
                current = current.tail.as_ref().unwrap();
            }
            &current.head
        }
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
}
