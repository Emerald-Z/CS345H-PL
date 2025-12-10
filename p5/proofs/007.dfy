lemma {:induction false} ChooseSymmetryProof(n: nat, r: nat)
    requires r <= n
    ensures choose(n, r) == choose(n, n - r)
{
    if r == 0 || r == n {
        // assert choose(n, r) == choose(n, n - r);
    } else {
        ChooseSymmetryProof(n - 1, r - 1);
        ChooseSymmetryProof(n - 1, r);
    }
}

lemma {:induction false} ChooseIncreasesProof(n: nat, r: nat)
    requires r <= n
    ensures choose(n, r) <= choose(n + 1, r)
{
    if r == 0 || r == n {
        // assert choose(n, r) <= choose(n + 1, r);
    } else {
        ChooseIncreasesProof(n - 1, r - 1);
        ChooseIncreasesProof(n - 1, r);
    }
}

lemma {:induction false} ChooseOneProof(n: nat)
    requires 1 <= n
    ensures choose(n, 1) == n
{
    if n == 1 {
        assert choose(1, 1) == 1;
    } else {
        ChooseOneProof(n - 1);
        assert choose(n, 1) == choose(n - 1, 0) + choose(n - 1, 1);
        assert choose(n - 1, 0) == 1;
        assert choose(n - 1, 1) == n - 1;
        assert choose(n, 1) == 1 + (n - 1);
        assert choose(n, 1) == n;
    }
}

lemma {:induction false} ChooseAbsorptionProof(n: nat, r: nat)
    requires 1 <= r <= n
    ensures r * choose(n, r) == n * choose(n - 1, r - 1)
{
    if n == 1 {
        assert r == 1;
        assert 1 * choose(1, 1) == 1 * choose(0, 0);
    } else if r == 1 {
        ChooseOneProof(n);
        assert choose(n, 1) == n;
        assert choose(n - 1, 0) == 1;
        assert 1 * choose(n, 1) == n * choose(n - 1, 0);
    } else if r == n {
        assert choose(n, n) == 1;
        assert choose(n - 1, n - 1) == 1;
        assert n * choose(n, n) == n * choose(n - 1, n - 1);
    } else {
        ChooseAbsorptionProof(n - 1, r - 1);
        ChooseAbsorptionProof(n - 1, r);
        assert choose(n, r) == choose(n - 1, r - 1) + choose(n - 1, r);
        assert r * choose(n, r) == r * (choose(n - 1, r - 1) + choose(n - 1, r));
        assert r * choose(n, r) == r * choose(n - 1, r - 1) + r * choose(n - 1, r);
        // From induction: (r - 1) * choose(n - 1, r - 1) == (n - 1) * choose(n - 2, r - 2)
        // So: r * choose(n - 1, r - 1) == choose(n - 1, r - 1) + (r - 1) * choose(n - 1, r - 1)
        // == choose(n - 1, r - 1) + (n - 1) * choose(n - 2, r - 2)
        // From induction: r * choose(n - 1, r) == (n - 1) * choose(n - 2, r - 1)
        assert (r - 1) * choose(n - 1, r - 1) == (n - 1) * choose(n - 2, r - 2);
        assert r * choose(n - 1, r) == (n - 1) * choose(n - 2, r - 1);
        assert r * choose(n - 1, r - 1) == choose(n - 1, r - 1) + (r - 1) * choose(n - 1, r - 1);
        assert r * choose(n - 1, r - 1) == choose(n - 1, r - 1) + (n - 1) * choose(n - 2, r - 2);
        assert r * choose(n, r) == choose(n - 1, r - 1) + (n - 1) * choose(n - 2, r - 2) + (n - 1) * choose(n - 2, r - 1);
        assert r * choose(n, r) == choose(n - 1, r - 1) + (n - 1) * (choose(n - 2, r - 2) + choose(n - 2, r - 1));
        assert choose(n - 1, r - 1) == choose(n - 2, r - 2) + choose(n - 2, r - 1);
        assert r * choose(n, r) == choose(n - 1, r - 1) + (n - 1) * choose(n - 1, r - 1);
        assert r * choose(n, r) == n * choose(n - 1, r - 1);
    }
}

// Exp(2, n) >= 1 for all n
lemma {:induction false} ExpPositive(n: nat)
    ensures Exp(2, n) >= 1
    decreases n
{
    if n == 0 {
        assert Exp(2, 0) == 1;
    } else {
        ExpPositive(n - 1);
        assert Exp(2, n) == 2 * Exp(2, n - 1);
        assert Exp(2, n - 1) >= 1;
        assert Exp(2, n) >= 2;
    }
}

lemma {:induction false} ChooseUpperBoundProof(n: nat, r: nat)
    requires r <= n
    ensures choose(n, r) <= Exp(2, n)
{
    ExpPositive(n);
    if r == 0 {
        assert choose(n, 0) == 1;
        assert choose(n, r) <= Exp(2, n);
    } else if r == n {
        assert choose(n, n) == 1;
        assert choose(n, r) <= Exp(2, n);
    } else {
        ChooseUpperBoundProof(n - 1, r - 1);
        ChooseUpperBoundProof(n - 1, r);
        assert choose(n, r) == choose(n - 1, r - 1) + choose(n - 1, r);
        assert choose(n - 1, r - 1) <= Exp(2, n - 1);
        assert choose(n - 1, r) <= Exp(2, n - 1);
        assert choose(n, r) <= Exp(2, n - 1) + Exp(2, n - 1);
        assert choose(n, r) <= 2 * Exp(2, n - 1);
        assert Exp(2, n) == 2 * Exp(2, n - 1);
        assert choose(n, r) <= Exp(2, n);
    }
}