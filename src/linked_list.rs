use crate::node::Node;
use vstd::prelude::*;

verus! {
    #[verifier(external_fn_specification)]
    pub fn ex_box_new<T>(value: T) -> Box<T> {
        Box::new(value)
    }

    #[derive(Debug, Clone)]
    pub struct LinkedList<T>(pub Option<Node<T>>);

    pub closed spec fn make_T<T>() -> T; // ghost constructor used in View and DeepView

    impl<T> View for LinkedList<T> {
        type V = Seq<T>;

        open spec fn view(&self) -> Seq<T> {
            match &self.0 {
                Some(node) => node.view(),
                None => Seq::new(0, |i: int| make_T()),
            }
        }
    }

    impl<T: DeepView> DeepView for LinkedList<T> {
        type V = Seq<T::V>;

        open spec fn deep_view(&self) -> Seq<T::V> {
            match &self.0 {
                Some(node) => node.deep_view(),
                None => Seq::new(0, |i: int| make_T()),
            }
        }
    }

    impl<T> Default for LinkedList<T> {
        fn default() -> Self {
            LinkedList::new()
        }
    }

    impl <T> LinkedList<T> {
        pub open spec fn spec_len(&self) -> nat {
            self.view().len()
        }

        pub open spec fn spec_index(&self, i: int) -> T {
            self.view().index(i)
        }

        pub open spec fn valid(&self) -> bool
            decreases self@.len()
        {
            ||| self.0 matches None && self@.len() == 0
            ||| self.0 matches Some(node) && node.valid()
        }

        pub fn new() -> (list: Self)
            ensures
                list.valid(),
                list@.len() == 0,
        {
            LinkedList(None)
        }

        pub proof fn length_content_equivalence(&self)
            requires
                self.valid(),
            ensures
                self@.len() == 0 <==> self.0.is_none(),
                self@.len() > 0 <==> self.0.is_some(),
        {
        }

        pub fn push(&mut self, value: T)
            requires
                old(self).valid(),
                old(self)@.len() < usize::MAX,
            ensures
                self.valid(),
                self@.len() == old(self)@.len() + 1,
                self@[0] == value,
                forall|i: int| 0 <= i < old(self)@.len() ==> self@[i + 1] == old(self)@[i],
        {
            let new_node = match self.0.take() {
                Some(node) => node.push(value),
                None => Node::new(value),
            };
            self.0 = Some(new_node);
        }

        pub fn pop(&mut self) -> (popped: Option<T>)
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
            match self.0.take() {
                Some(node) => {
                    let (value, new_node) = node.pop();
                    self.0 = new_node;
                    Some(value)
                }
                None => None,
            }
        }
    }
}
