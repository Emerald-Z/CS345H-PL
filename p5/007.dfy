// Combination: C(n, r).
function {:induction false} choose(n: nat, r: nat) : nat
    requires r <= n
    decreases n, r
{
    if r == 0 || r == n then 1 // Only one way to choose (none or all).
    else choose(n - 1, r - 1) + choose(n - 1, r) // Pascal's Identity.
}

// Helper function for a proof. Takes base to the power of exponent.
function {:induction false} Exp(base: nat, exponent: nat): nat
{
    if exponent == 0 then 1
    else base * Exp(base, exponent - 1)
}

// Proofs:

// C(n, r) == C(n, n - r)
method {:induction false} ChooseSymmetryTest(n: nat, r: nat)
    requires r <= n
{
    assert choose(n, r) == choose(n, n - r) by {
        ChooseSymmetryProof(n, r);
    }
}

// C(n, r) <= C(n + 1, r)
method {:induction false} ChooseIncreasesTest(n: nat, r: nat)
    requires r <= n
{
    assert choose(n, r) <= choose(n + 1, r) by {
        ChooseIncreasesProof(n, r);
    }
}

// C(n, 1) == n
method {:induction false} ChooseOneTest(n: nat)
    requires 1 <= n
{
    assert choose(n, 1) == n by {
        ChooseOneProof(n);
    }
}

// r * C(n, r) == n * C(n - 1, r - 1)
method {:induction false} ChooseAbsorptionTest(n: nat, r: nat)
    requires 1 <= r <= n
{
    assert r * choose(n, r) == n * choose(n - 1, r - 1) by {
        ChooseAbsorptionProof(n, r);
    }
}

// C(n, r) <= 2^n
method {:induction false} ChooseUpperBoundTest(n: nat, r: nat)
    requires r <= n
{
    assert choose(n, r) <= Exp(2, n) by {
        ChooseUpperBoundProof(n, r);
    }
}

