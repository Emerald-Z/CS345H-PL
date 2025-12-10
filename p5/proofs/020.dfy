// elements are swapped, and all other elements are unchanged
predicate {:induction false} swapInvariant(listIn: seq<int>, listOut: seq<int>, i: nat, j: nat)
    requires i <= j < |listIn| == |listOut|
{
    listOut[i] == listIn[j] && 
    listOut[j] == listIn[i] &&
    forall k :: (0 <= k < |listIn| && k != i && k != j) ==> listOut[k] == listIn[k]
}

// Inner loop invariant: after j iterations, element at j is gt all in 0..j-1 
predicate {:induction false} innerLoopInvariant(listIn: seq<int>, listOut: seq<int>, i: nat, j: nat)
    requires j < i <= |listIn| == |listOut|
{
    (j == 0 || (forall k :: 0 <= k < j ==> listOut[k] <= listOut[j])) &&
    listOut[i..] == listIn[i..] // suffix at i should be unchanged
}

// Outer loop invariant: the last (|list| - i) elements are sorted and are all lt elements before
predicate {:induction false} outerLoopInvariant(list: seq<int>, i: nat)
    requires i <= |list|
{
    sorted(list[i..]) &&
    (forall k, m :: 0 <= k < i && i <= m < |list| ==> list[k] <= list[m])
}
