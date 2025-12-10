lemma {:induction false} ReverseConcat(a: seq<int>, b: seq<int>)
    ensures Reverse(a + b) == Reverse(b) + Reverse(a)
{
    if |a| == 0 {
        // Base case: Reverse([] + b) == Reverse(b) == Reverse(b) + [] == Reverse(b) + Reverse([])
        assert a + b == b;
        assert Reverse(a) == [];
    } else {
        ReverseConcat(a[1..], b);
        // When |a| > 0, we have (a + b)[0] == a[0] and (a + b)[1..] == a[1..] + b
        assert (a + b)[0] == a[0];
        assert (a + b)[1..] == a[1..] + b;
    }
}

lemma {:induction false} DoubleReverseLemma(s: seq<int>)
    ensures Reverse(Reverse(s)) == s
{
    if |s| == 0 {
        // Base case: Reverse(Reverse([])) = []
    } else {
        DoubleReverseLemma(s[1..]);
        // Reverse(Reverse(s[1..])) = s[1..]

        assert s == [s[0]] + s[1..];
        assert Reverse(s) == Reverse(s[1..]) + [s[0]];
        assert Reverse(Reverse(s)) == Reverse(Reverse(s[1..]) + [s[0]]);

        // need to show that Reverse(a + b) == Reverse(b) + Reverse(a) last item is first
        ReverseConcat(Reverse(s[1..]), [s[0]]);
        assert Reverse(Reverse(s[1..]) + [s[0]]) == Reverse([s[0]]) + Reverse(Reverse(s[1..]));
        
        assert Reverse([s[0]]) == [s[0]];
        
        assert Reverse(Reverse(s)) == Reverse([s[0]]) + Reverse(Reverse(s[1..]));
        assert Reverse(Reverse(s)) == [s[0]] + Reverse(Reverse(s[1..]));
        assert Reverse(Reverse(s)) == [s[0]] + s[1..];
        assert Reverse(Reverse(s)) == s;
    }
}