lemma {:induction false} Proof(n : int)
    requires n > 0
    ensures Sequence(n) == n * (n + 1) / 2
{
    if n == 1 {
        // base case
    } else {
        Proof(n - 1);
        // Sequence(n-1) == (n-1) * (n) / 2
        assert Sequence(n) == n + Sequence(n - 1);
        assert Sequence(n) == n + (n-1) * (n) / 2;
        assert Sequence(n) == n * (n + 1) / 2;
    }
}