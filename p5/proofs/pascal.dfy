// SumPascalRow(n, k) = SumPascalRow(n-1, k-1) + SumPascalRow(n-1, k) when 0 < k <= n
lemma {:induction false} SumPascalRelation(n: nat, k: nat)
    requires n > 0 && 0 < k <= n
    ensures SumPascalRow(n, k) == SumPascalRow(n-1, k-1) + SumPascalRow(n-1, k)
    decreases k
{
    if k == 1 {
        // base case
    } else {
        SumPascalRelation(n, k-1);
    }
}

// SumPascalRow(n, n) = 2 * SumPascalRow(n-1, n-1) because each element is used twice in the summation
lemma {:induction false} PascalHelper(n: nat)
    requires n > 0
    ensures SumPascalRow(n, n) == 2 * SumPascalRow(n-1, n-1)
{
    if n == 1 {
        // Base case: SumPascalRow(1, 1) = 2, SumPascalRow(0, 0) = 1
    } else {
        SumPascalRelation(n, n);
        // SumPascalRow(n, n) == SumPascalRow(n-1, n-1) + SumPascalRow(n-1, n)
        // Pascal(n-1, n) = 0 so SumPascalRow(n-1, n) = SumPascalRow(n-1, n-1)
        assert SumPascalRow(n-1, n) == SumPascalRow(n-1, n-1);
    }
}

lemma {:induction false} PascalRowSumProof(n: nat)
    ensures Pow(2, n) == SumPascalRow(n, n)
{
    if n == 0 {
        // Base case: Pow(2, 0) = 1, SumPascalRow(0, 0) = 1
    } else {
        PascalRowSumProof(n-1);
        //Pow(2, n-1) == SumPascalRow(n-1, n-1)
        PascalHelper(n);
        //SumPascalRow(n, n) == 2 * SumPascalRow(n-1, n-1)
        assert Pow(2, n) == 2 * Pow(2, n-1);
        assert SumPascalRow(n, n) == Pow(2, n);
    }
}
