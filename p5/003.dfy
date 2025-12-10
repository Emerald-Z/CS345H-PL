// A binary search tree implementation with an insertion method 
// The proof is to show that inserting any integer value maintains the BST property

datatype BSTNode = 
      Blank
    | Node(value: int, left: BSTNode, right: BSTNode)

function {:induction false} Values(root: BSTNode): set<int> 
    decreases root
{
    match root {
        case Blank => {}
        case Node(v, left, right) => Values(left) + {v} + Values(right)
    }
}

predicate {:induction false} IsBST(root: BSTNode)
    decreases root
{
    match root {
        case Blank => true
        case Node(v, left, right) => 
            (forall x :: x in Values(left) ==> x < v) &&
            (forall x :: x in Values(right) ==> x > v) &&
            IsBST(left) &&
            IsBST(right)
    }
}

// NOTE: inserting a value already in the BST doesn't change the tree
function {:induction false} Insert(root: BSTNode, value: int): BSTNode 
    requires IsBST(root)
    decreases root 
{
    match root {
        case Blank => Node(value, Blank, Blank)
        case Node(v, left, right) => 
            if value < v then 
                Node(v, Insert(left, value), right) 
            else if value > v then
                Node(v, left, Insert(right, value))
            else 
                root
    }
}

method BSTInsertionTest(root: BSTNode, x: int) 
    requires IsBST(root)
    ensures IsBST(Insert(root, x))
{
    assert IsBST(root) ==> IsBST(Insert(root, x)) by {

        // HINT: start by showing that inserting x into a tree adds x to the set of values of the tree
        BSTInsertionProof(root, x);
    }
}