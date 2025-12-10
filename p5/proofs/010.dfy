predicate Sorted(s: seq<int>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

predicate Permutation(a: seq<int>, b: seq<int>)
{
    |a| == |b| && multiset(a) == multiset(b)
}

// The first i elements are sorted and are the i smallest elements
predicate Outer_Loop_Invariant(sorted: seq<int>, i: int)
{
    0 <= i <= |sorted| &&
    (forall k, l :: 0 <= k < l < i ==> sorted[k] <= sorted[l]) &&
    (forall k, l :: 0 <= k < i <= l < |sorted| ==> sorted[k] <= sorted[l])
}

// min is the index of the minimum element in sorted[i..j)
predicate Inner_Loop_Invariant(sorted: seq<int>, min: int, i: int, j: int)
    requires 0 <= i < j <= |sorted|
{
    i <= min < |sorted| &&
    i < j <= |sorted| &&
    i <= min < j &&
    (forall k :: i <= k < j ==> sorted[min] <= sorted[k])
}


