lemma {:induction false} SumConcat(a: seq<int>, b: seq<int>)
    ensures Sum(a + b) == Sum(a) + Sum(b)
{
    if |a| == 0 {
        // Base case: Sum([] + b) == Sum([]) + Sum(b) == 0 + Sum(b) == Sum(b)
        assert a + b == b;
    } else {
        SumConcat(a[1..], b);
        // Sum(a + b) == a[0] + Sum((a + b)[1..])
        assert (a + b)[1..] == a[1..] + b;
    }
}

lemma {:induction false} Prove_TreeSize(t: Tree)
    ensures Size(t) == |Flatten(t)|
{
    match t
    case Leaf(_) =>
        // Base case: Size(Leaf) = 1, |Flatten(Leaf)| = 1
    case Node(l, _, r) =>
        Prove_TreeSize(l);
        Prove_TreeSize(r);
        // Size(Node(l, _, r)) == Size(l) + 1 + Size(r)
        // |Flatten(Node(l, _, r))| == |Flatten(l)| + 1 + |Flatten(r)|
        assert Size(t) == Size(l) + 1 + Size(r);
        assert |Flatten(t)| == |Flatten(l)| + 1 + |Flatten(r)|;
}

lemma {:induction false} Prove_TreeSum(t: Tree)
    ensures SumTree(t) == Sum(Flatten(t))
{
    match t
    case Leaf(v) =>
        // Base case: SumTree(Leaf) = v, Sum(Flatten(Leaf)) = v
    case Node(l, v, r) =>
        Prove_TreeSum(l);
        Prove_TreeSum(r);
        // SumTree(l) == Sum(Flatten(l)) and SumTree(r) == Sum(Flatten(r))
        assert SumTree(l) == Sum(Flatten(l));
        assert SumTree(r) == Sum(Flatten(r));

        assert SumTree(t) == SumTree(l) + v + SumTree(r);
        assert Flatten(t) == Flatten(l) + [v] + Flatten(r);

        // prove concatenation of lists is associative
        SumConcat(Flatten(l) + [v], Flatten(r));
        SumConcat(Flatten(l), [v]);

        calc {
            Sum(Flatten(t));
        == 
            Sum(Flatten(l) + [v] + Flatten(r));
        ==  // Sum((Flatten(l) + [v]) + Flatten(r)) == Sum(Flatten(l) + [v]) + Sum(Flatten(r))
            Sum(Flatten(l) + [v]) + Sum(Flatten(r));
        == 
            Sum(Flatten(l)) + Sum([v]) + Sum(Flatten(r));
        ==  
            Sum(Flatten(l)) + v + Sum(Flatten(r)); // Sum([v]) == v
        == 
            SumTree(l) + v + SumTree(r);
        == 
            SumTree(t); // def
        }
}