// produces a sequence of the correct length
lemma {:induction false} Repeat_Length(x: int, n: nat)
    ensures |Repeat(x, n)| == n
{
    if n == 0 {
    } else {
        Repeat_Length(x, n-1);
        assert |Repeat(x, n)| == 1 + |Repeat(x, n-1)|;
        assert |Repeat(x, n)| == n;
    }
}

lemma {:induction false} Prove_Volume(rle: seq<Pair>)
    ensures |Decompression(rle)| == TotalCount(rle)
{
    if |rle| == 0 {
        // Base case: Decompression([]) = [] and TotalCount([]) = 0, so |[]| == 0
    } else {
        Repeat_Length(rle[0].val, rle[0].count);
        Prove_Volume(rle[1..]);
        // function definition when |rle| > 0:
        assert Decompression(rle) == Repeat(rle[0].val, rle[0].count) + Decompression(rle[1..]);
        // function definition:
        assert TotalCount(rle) == rle[0].count + TotalCount(rle[1..]);
        calc {
            |Decompression(rle)|;
        ==
            |Repeat(rle[0].val, rle[0].count) + Decompression(rle[1..])|;
        ==  // length of concatenated sequences is sum of lengths
            |Repeat(rle[0].val, rle[0].count)| + |Decompression(rle[1..])|;
        ==  // by Repeat_Length lemma
            rle[0].count + |Decompression(rle[1..])|;
        ==  // by induction hypothesis
            rle[0].count + TotalCount(rle[1..]);
        ==  // by definition of TotalCount
            TotalCount(rle);
        }
    }
}

lemma {:induction false} Prove_Parallel_Decompression(a: seq<Pair>, b: seq<Pair>)
    ensures Decompression(a + b) == Decompression(a) + Decompression(b)
{
    if |a| == 0 {
        // Base case: a is empty
        assert a + b == b;
        assert Decompression(a) == [];
        assert Decompression(a + b) == Decompression(b);
        assert Decompression(a) + Decompression(b) == Decompression(b);
        assert Decompression(a + b) == Decompression(a) + Decompression(b);
    } else {
        Prove_Parallel_Decompression(a[1..], b);
        // From function definition when |a + b| > 0 (which is true since |a| > 0):
        assert Decompression(a + b) == Repeat((a + b)[0].val, (a + b)[0].count) + Decompression((a + b)[1..]);
        assert (a + b)[0] == a[0];
        assert (a + b)[1..] == a[1..] + b;
        assert Decompression(a) == Repeat(a[0].val, a[0].count) + Decompression(a[1..]);
        calc {
            Decompression(a + b);
        ==
            Repeat((a + b)[0].val, (a + b)[0].count) + Decompression((a + b)[1..]);
        ==
            Repeat(a[0].val, a[0].count) + Decompression(a[1..] + b);
        ==  // by induction hypothesis
            Repeat(a[0].val, a[0].count) + (Decompression(a[1..]) + Decompression(b));
        ==
            (Repeat(a[0].val, a[0].count) + Decompression(a[1..])) + Decompression(b);
        ==  // by definition of Decompression(a)
            Decompression(a) + Decompression(b);
        }
    }
}