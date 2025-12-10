lemma {:induction false} MapSizeProof(f: int -> int, x : seq<int>)
    requires |x| > 0
    ensures |Map(f, x)| == |x|
    decreases |x|
{
    if |x| == 1 {
        assert Map(f, x) == [f(x[0])];
        assert |Map(f, x)| == 1;
        assert |x| == 1;
    } else {
        MapSizeProof(f, x[1..]);
        assert |Map(f, x)| == |x[1..]| + 1;
        assert |x| == |x[1..]| + 1;
    }
}

lemma {:induction false} MapProof(f: int -> int, x : seq<int>)
    requires |x| > 0
    requires |x| == |Map(f, x)|
    ensures forall i :: 0 <= i < |x| ==> f(x[i]) == Map(f, x)[i]
    decreases |x|
{
    if |x| == 1 {
        assert Map(f, x) == [f(x[0])];
        assert |Map(f, x)| == 1;
        assert |x| == 1;
    } else {
        MapProof(f, x[1..]);
        assert |Map(f, x)| == |x[1..]| + 1;
        assert |x| == |x[1..]| + 1;
    }
}

lemma {:induction false} ProveMapReduce(f: int -> int, x : seq<int>)
    requires |x| > 0
    ensures MapReduce(f, x) == MapReduceSpec(f, x)
    decreases |x|
{
    if |x| == 1 {
        assert MapReduce(f, x) == f(x[0]);
        assert MapReduceSpec(f, x) == f(x[0]);
    } else {
        ProveMapReduce(f, x[1..]);
        assert MapReduce(f, x) == f(x[0]) + MapReduce(f, x[1..]);
        assert MapReduceSpec(f, x) == f(x[0]) + MapReduceSpec(f, x[1..]);
    }
}

lemma {:induction false} FilterTrueProof(p: int -> bool, x : seq<int>)
    requires |x| > 0
    ensures forall i :: 0 <= i < |Filter(p, x)| ==> p(Filter(p, x)[i])
    decreases |x|
{
    if |x| == 1 {
        // If p(x[0]) is true, Filter(p, x) == [x[0]], otherwise Filter(p, x) == []
    } else {
        FilterTrueProof(p, x[1..]);
        // Filter(p, x) = [x[0]] + Filter(p, x[1..]) or Filter(p, x[1..])
    }
}

lemma {:induction false} FilterSubsetProof(p: int -> bool, x : seq<int>)
    requires |x| > 0
    ensures forall i :: 0 <= i < |Filter(p, x)| ==> Filter(p, x)[i] in x
    decreases |x|
{
    if |x| == 1 {
        // If p(x[0]), then Filter(p, x) == [x[0]] and x[0] in x otherwise Filter(p, x) == []
    } else {
        FilterSubsetProof(p, x[1..]);
        // If p(x[0]), Filter(p, x) == [x[0]] + Filter(p, x[1..])
        // else Filter(p, x) == Filter(p, x[1..])
        assert forall i :: 0 <= i < |x[1..]| ==> x[1..][i] in x;
    }
}

lemma {:induction false} FilterCompleteProof(p: int -> bool, x : seq<int>)
    requires |x| > 0
    ensures forall i :: 0 <= i < |x| && p(x[i]) ==> x[i] in Filter(p, x)
    decreases |x|
{
    if |x| == 1 {
        // If p(x[0]), then Filter(p, x) == [x[0]] so x[0] in Filter(p, x)
    } else {
        FilterCompleteProof(p, x[1..]);
        assert forall i :: 1 <= i < |x| ==> x[i] in x[1..];
    }
}