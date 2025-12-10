// Part 1: Defines simple linear and binary search functions on sequences of integers
// Tests that on a sorted sequence, both searches return the same result
// Required lemma statements are commented below tests

predicate Sorted(s: seq<int>)
{
  forall i, j | 0 <= i < j < |s| :: s[i] <= s[j]
}

// Linear search: return index of first occurrence, or -1 if not found.
function {:induction false} LinearSearch(s: seq<int>, k: int): int
  decreases |s|
{
  if |s| == 0 then -1
  else if s[0] == k then 0
  else var t := LinearSearch(s[1..], k); if t == -1 then -1 else t + 1
}

// Binary search: requires sorted sequence and returns the index of the first occurrence, or -1 if not found.
function {:induction false} BinarySearch(s: seq<int>, k: int): int
  requires Sorted(s)
  decreases |s|
{
  if |s| == 0 then -1
  else
    var mid := |s| / 2;
    if s[mid] < k then
      var r := BinarySearch(s[mid+1..], k);
      if r == -1 then -1 else r + mid + 1
    else if s[mid] > k then
      BinarySearch(s[..mid], k)
    else
      var left := BinarySearch(s[..mid], k);
      if left == -1 then mid else left
}

// Test method that uses hard coded sequences to verify LinearSearch and BinarySearch agree
method {:induction false} {:verify true} TestLinearEqualsBinary()
{
  // basic sorted list
  var s1 := [1, 2, 3, 4];
  assert Sorted(s1);
  assert LinearSearch(s1, 3) == BinarySearch(s1, 3) by { LinearEqualsBinary(s1, 3); }
  assert LinearSearch(s1, 5) == BinarySearch(s1, 5) by { LinearEqualsBinary(s1, 5); }

  // list with duplicates
  var s2 := [1, 2, 2, 2, 3];
  assert Sorted(s2);
  assert LinearSearch(s2, 2) == BinarySearch(s2, 2) by { LinearEqualsBinary(s2, 2); }

  // empty list (should get -1)
  var s3 := [];
  assert Sorted(s3);
  assert LinearSearch(s3, 7) == BinarySearch(s3, 7) by { LinearEqualsBinary(s3, 7); }

  // list with multiple duplicates
  var s4 := [0, 0, 1, 1, 2, 3];
  assert Sorted(s4);
  assert LinearSearch(s4, 0) == BinarySearch(s4, 0) by { LinearEqualsBinary(s4, 0); }
  assert LinearSearch(s4, 3) == BinarySearch(s4, 3) by { LinearEqualsBinary(s4, 3); }
}

// General test method that can be called with any sorted sequence and key
method {:induction false} {:verify true} TestLinearEqualsBinaryGeneral(s: seq<int>, k: int)
  requires Sorted(s)
{
  assert LinearSearch(s, k) == BinarySearch(s, k) by { LinearEqualsBinary(s, k); }
}

// Specification lemmas for LinearSearch and BinarySearch
method {:induction false} {:verify true} TestLinearSearchSpec(s: seq<int>, k: int)
{
  // verify that if it returns -1, k is not in s, and if it returns an index, that index is valid and points to k
  assert (LinearSearch(s, k) == -1) <==> (forall i | 0 <= i < |s| :: s[i] != k) by { LinearSearch_Spec(s, k); }
  assert LinearSearch(s, k) != -1 ==> 0 <= LinearSearch(s,k) < |s| by { LinearSearch_Spec(s, k); }
  assert LinearSearch(s, k) != -1 ==> s[LinearSearch(s,k)] == k by { LinearSearch_Spec(s, k); }
  assert LinearSearch(s, k) != -1 ==> forall j | 0 <= j < LinearSearch(s,k) :: s[j] != k by { LinearSearch_Spec(s, k); }
}

// same as above but for BinarySearch requiring Sorted(s)
method {:induction false} {:verify true} TestBinarySearchSpec(s: seq<int>, k: int)
  requires Sorted(s)
{
  assert (BinarySearch(s, k) == -1) <==> (forall i | 0 <= i < |s| :: s[i] != k) by { BinarySearch_Spec(s, k); }
  assert BinarySearch(s, k) != -1 ==> 0 <= BinarySearch(s,k) < |s| by { BinarySearch_Spec(s, k); }
  assert BinarySearch(s, k) != -1 ==> s[BinarySearch(s,k)] == k by { BinarySearch_Spec(s, k); }
  assert BinarySearch(s, k) != -1 ==> forall j | 0 <= j < BinarySearch(s,k) :: s[j] != k by { BinarySearch_Spec(s, k); }
}

// lemma {:induction false} LinearEqualsBinary(s: seq<int>, k: int)
//   requires Sorted(s)
//   ensures LinearSearch(s, k) == BinarySearch(s, k)
// {
// }

// lemma {:induction false} LinearSearch_Spec(s: seq<int>, k: int)
//   ensures (LinearSearch(s, k) == -1) <==> (forall i | 0 <= i < |s| :: s[i] != k)
//   ensures LinearSearch(s, k) != -1 ==> 0 <= LinearSearch(s,k) < |s|
//   ensures LinearSearch(s, k) != -1 ==> s[LinearSearch(s,k)] == k
//   ensures LinearSearch(s, k) != -1 ==> forall j | 0 <= j < LinearSearch(s,k) :: s[j] != k
// {

// lemma {:induction false} BinarySearch_Spec(s: seq<int>, k: int)
//   requires Sorted(s)
//   ensures (BinarySearch(s, k) == -1) <==> (forall i | 0 <= i < |s| :: s[i] != k)
//   ensures BinarySearch(s, k) != -1 ==> 0 <= BinarySearch(s,k) < |s|
//   ensures BinarySearch(s, k) != -1 ==> s[BinarySearch(s,k)] == k
//   ensures BinarySearch(s, k) != -1 ==> forall j | 0 <= j < BinarySearch(s,k) :: s[j] != k
// {
// }








// Part 2: Defines a simple BST with add and in order traversal
// Tests that adding to BST maintains sortedness of tree and that in order traversal returns a sorted sequence
// Required lemma statements are commented below tests

datatype BST = Null | Node(value: int, left: BST, right: BST)

// reuses sorted predicate from above

predicate {:induction false} AllLessEqual(t: BST, x: int)
{
  match t
  case Null => true
  case Node(v, l, r) =>
    v <= x &&
    AllLessEqual(l, x) &&

    AllLessEqual(r, x)
}
predicate {:induction false} AllGreaterEqual(t: BST, x: int)
{
  match t
  case Null => true
  case Node(v, l, r) =>
    v >= x &&
    AllGreaterEqual(l, x) &&
    AllGreaterEqual(r, x)
}

predicate {:induction false} TreeSorted(t: BST)
{
  match t
  case Null => true
  case Node(v, l, r) =>
    AllLessEqual(l, v) &&
    AllGreaterEqual(r, v) &&
    TreeSorted(l) &&
    TreeSorted(r)
}

function {:induction false} InOrder(t: BST): seq<int>
{
  match t
  case Null => []
  case Node(v,l,r) => InOrder(l) + [v] + InOrder(r)
}

function {:induction false} Insert(t: BST, x: int): BST
{
  match t
  case Null => Node(x, Null, Null)
  case Node(v,l,r) =>
    if x <= v then Node(v, Insert(l,x), r) else Node(v, l, Insert(r,x))
}

method {:induction false} TestInsertPreservesTreeSorted(t: BST, x: int)
  requires TreeSorted(t)
{
  assert TreeSorted(Insert(t, x)) by {
    InsertPreservesTreeSorted(t, x);
  }
}

method {:induction false} TestInsertPreservesSorted(t: BST, x: int)
  requires TreeSorted(t)
{
  assert Sorted(InOrder(Insert(t, x))) by {
    InsertPreservesSorted(t, x);
  }
}

method {:induction false} TestTreeSortedImpliesSorted(t: BST)
  requires TreeSorted(t)
{
  assert Sorted(InOrder(t)) by {
    TreeSortedImpliesSorted(t);
  }
}

method {:induction false} TestSortedImpliesTreeSorted(t: BST)
  requires Sorted(InOrder(t))
{
  assert TreeSorted(t) by {
    SortedImpliesTreeSorted(t);
  }
}

// lemma {:induction false} TreeSortedImpliesSorted(t: BST)
//   requires TreeSorted(t)
//   ensures Sorted(InOrder(t))
// {
// }

// lemma {:induction false} SortedImpliesTreeSorted(t: BST)
//   requires Sorted(InOrder(t))
//   ensures TreeSorted(t)
// {
// }

// lemma {:induction false} InsertPreservesTreeSorted(t: BST, x: int)
//   requires TreeSorted(t)
//   ensures TreeSorted(Insert(t, x))
// {
// }

// lemma {:induction false} InsertPreservesSorted(t: BST, x: int)
//   requires TreeSorted(t)
//   ensures Sorted(InOrder(Insert(t, x)))
// {
// }

