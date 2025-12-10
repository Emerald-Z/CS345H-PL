// hinted: Values of a subtree are a subset of Values of the parent 
lemma {:induction false} ValuesSubset(root: BSTNode, subtree: BSTNode)
    requires IsBST(root)
    requires subtree == root || (match root {
        case Node(v, left, right) => subtree == left || subtree == right
        case Blank => false
    })
    ensures Values(subtree) <= Values(root)
    decreases root
{
    match root {
        case Blank => {
        }
        case Node(v, left, right) => {
            if subtree == left || subtree == right {
                assert Values(root) == Values(left) + {v} + Values(right);
            }
        }
    }
}

// If all values in a BST are < bound and we insert value < bound, result still has all values < bound
lemma {:induction false} InsertPreservesOrdering(root: BSTNode, value: int, bound: int, isLess: bool)
    requires IsBST(root)
    requires isLess ==> (forall x :: x in Values(root) ==> x < bound) && value < bound
    requires !isLess ==> (forall x :: x in Values(root) ==> x > bound) && value > bound
    ensures isLess ==> forall x :: x in Values(Insert(root, value)) ==> x < bound
    ensures !isLess ==> forall x :: x in Values(Insert(root, value)) ==> x > bound
    decreases root
{
    match root {
        case Blank => {
            if isLess {
                assert Values(Insert(root, value)) == {value};
            } else {
                assert Values(Insert(root, value)) == {value};
            }
        }
        case Node(v, left, right) => {
            assert v in Values(root);
            if isLess {
                assert v < bound;
                assert forall x :: x in Values(left) ==> x < v;
                assert forall x :: x in Values(left) ==> x < bound;
                if value < v {
                    InsertPreservesOrdering(left, value, v, true);
                    assert forall x :: x in Values(Insert(left, value)) ==> x < v;
                    assert forall x :: x in Values(Insert(left, value)) ==> x < bound;
                } else if value > v {
                    assert Values(right) <= Values(root);
                    assert forall x :: x in Values(right) ==> x < bound;
                    InsertPreservesOrdering(right, value, bound, true);
                } else {
                    assert Insert(root, value) == root;
                }
            } else {
                assert v > bound;
                assert forall x :: x in Values(right) ==> x > v;
                assert forall x :: x in Values(right) ==> x > bound;
                if value > v {
                    InsertPreservesOrdering(right, value, v, false);
                    assert forall x :: x in Values(Insert(right, value)) ==> x > v;
                    assert forall x :: x in Values(Insert(right, value)) ==> x > bound;
                } else if value < v {
                    assert Values(left) <= Values(root);
                    assert forall x :: x in Values(left) ==> x > bound;
                    InsertPreservesOrdering(left, value, bound, false);
                } else {
                    assert Insert(root, value) == root;
                }
            }
        }
    }
}

lemma {:induction false} BSTInsertionProof(root: BSTNode, value: int)
    requires IsBST(root)
    ensures IsBST(Insert(root, value))
{
    match root {
        case Blank => {
            assert IsBST(Insert(root, value));
        }
        case Node(v, left, right) => {
            if value < v {
                BSTInsertionProof(left, value);
                assert IsBST(Insert(left, value));
                assert forall x :: x in Values(left) ==> x < v;
                InsertPreservesOrdering(left, value, v, true);
                assert forall x :: x in Values(Insert(left, value)) ==> x < v;
                assert IsBST(right);
                assert forall x :: x in Values(right) ==> x > v;
                assert IsBST(Insert(root, value));
            } else if value > v {
                BSTInsertionProof(right, value);
                assert IsBST(Insert(right, value));
                assert forall x :: x in Values(right) ==> x > v;
                InsertPreservesOrdering(right, value, v, false);
                assert forall x :: x in Values(Insert(right, value)) ==> x > v;
                assert IsBST(left);
                assert forall x :: x in Values(left) ==> x < v;
                assert IsBST(Insert(root, value));
            } else {
                assert Insert(root, value) == root;
                assert IsBST(Insert(root, value));
            }
        }
    }
}