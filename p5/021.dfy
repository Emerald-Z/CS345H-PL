// some functions we've talked about in this class
// sorry this got kinda long

// simplified Reduce that just sums
// can't reduce by other means
function {:induction false} Reduce(x: seq<int>) : int
    requires |x| > 0
{
    if |x| == 1 then x[0] else x[0] + Reduce(x[1..])
}

// Map works as expected
function {:induction false} Map(f: int -> int, x : seq<int>) : seq<int>
    requires |x| > 0
    //ensures |Map(f, x)| == |x|
{
    if |x| == 1 then [f(x[0])] else [f(x[0])] + Map(f, x[1..])
}

// MapReduce
function {:induction false} MapReduce(f: int -> int, x : seq<int>) : int
    requires |x| > 0
{
    Reduce(Map(f, x))
}

// Filter
function {:induction false} Filter(p: int -> bool, x : seq<int>) : seq<int>
    requires |x| > 0
{
    if |x| == 1 then
        if p(x[0]) then [x[0]] else []
    else
        if p(x[0]) then [x[0]] + Filter(p, x[1..]) else Filter(p, x[1..])
}

// -------------------------------------------------------------
// Specs to prove

function {:induction false} MapReduceSpec(f: int -> int, x: seq<int>) : int
    requires |x| > 0
{
    if |x| == 1 then f(x[0]) else f(x[0]) + MapReduceSpec(f, x[1..])
}

// ------------------------------------------------------------
// Actual tests

// Test that Map works as expected
// lemma stubs:
/*
lemma {:induction false} MapSizeProof(f: int -> int, x : seq<int>)
    requires |x| > 0
    ensures |Map(f, x)| == |x|
    decreases |x|
{
}

lemma {:induction false} MapProof(f: int -> int, x : seq<int>)
    requires |x| > 0
    requires |x| == |Map(f, x)|
    ensures forall i :: 0 <= i < |x| ==> f(x[i]) == Map(f, x)[i]
    decreases |x|
{
}

*/
method {:induction false} MapTest(f: int -> int, x : seq<int>)
    requires |x| > 0
{
    assert |Map(f, x)| == |x| by {
        MapSizeProof(f, x);
    }
    assert forall i :: 0 <= i < |x| ==> f(x[i]) == Map(f, x)[i] by {
        MapProof(f, x);
    }
}

// Test that MapReduce works as expected
// lemma stub:
/*
lemma {:induction false} ProveMapReduce(f: int -> int, x : seq<int>)
    requires |x| > 0
    ensures MapReduce(f, x) == MapReduceSpec(f, x)
    decreases |x|
{
}
*/
method {:induction false} MapReduceTest(f : int -> int, x : seq<int>) 
    requires |x| > 0
{
    assert MapReduce(f, x) == MapReduceSpec(f, x) by {
        ProveMapReduce(f, x);
    }
}

// test that filter works as expected
// lemma stubs:
/*
lemma {:induction false} FilterTrueProof(p: int -> bool, x : seq<int>)
    requires |x| > 0
    ensures forall i :: 0 <= i < |Filter(p, x)| ==> p(Filter(p, x)[i])
    decreases |x|
{
}

lemma {:induction false} FilterSubsetProof(p: int -> bool, x : seq<int>)
    requires |x| > 0
    ensures forall i :: 0 <= i < |Filter(p, x)| ==> Filter(p, x)[i] in x
    decreases |x|
{
}

lemma {:induction false} FilterCompleteProof(p: int -> bool, x : seq<int>)
    requires |x| > 0
    ensures forall i :: 0 <= i < |x| && p(x[i]) ==> x[i] in Filter(p, x)
    decreases |x|
{
}
*/
method {:induction false} FilterTest(p: int -> bool, x : seq<int>)
    requires |x| > 0
{
    var y := Filter(p, x);
    assert forall i :: 0 <= i < |y| ==> p(y[i]) by {
        FilterTrueProof(p, x);
    }

    assert forall i :: 0 <= i < |y| ==> y[i] in x by {
        FilterSubsetProof(p, x);
    }

    assert forall i :: 0 <= i < |x| && p(x[i]) ==> x[i] in y by {
        FilterCompleteProof(p, x);
    }
}