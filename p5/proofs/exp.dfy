lemma {:induction false} ExpPositiveProof(a: nat, x: nat)
    requires a > 0
    ensures exp(a, x) > 0
{
    if x == 0 {
        // Base case: exp(a, 0) = 1 > 0
    } else {
        ExpPositiveProof(a, x - 1);
        // exp(a, x-1) > 0

        assert exp(a, x) == a * exp(a, x - 1);
        assert a > 0;
        assert exp(a, x - 1) > 0;
        assert exp(a, x) > 0;
    }
}

lemma {:induction false} ExpIncreasingProof(a: nat, x: nat)
    requires a > 1
    ensures exp(a, x) < exp(a, x + 1)
{
    if x == 0 {
        // Base case: exp(a, 0) = 1 < exp(a, 1) = a
    } else {
        ExpIncreasingProof(a, x - 1);
        // exp(a, x-1) < exp(a, x)
        assert exp(a, x + 1) == a * exp(a, x);
        assert a > 1;
        assert exp(a, x) < exp(a, x + 1);
        
    }
}

lemma {:induction false} ExpAddProof(a: nat, x: nat, y: nat)
    requires a != 0 || (x != 0 && y != 0)
    ensures exp(a, x) * exp(a, y) == exp(a, x + y)
{
    if x == 0 || a == 0 {
        // Base case: exp(a, 0) = 1
    } else {
        ExpAddProof(a, x - 1, y);
        // exp(a, x-1) * exp(a, y) == exp(a, x + y)
        assert exp(a, x) == a * exp(a, x - 1);
        assert exp(a, x + y) == a * exp(a, x + y - 1);
    }
}

lemma {:induction false} ExpMulProof(a: nat, b: nat, x: nat)
    requires (a != 0 && b != 0) || x != 0
    ensures exp(a, x) * exp(b, x) == exp(a * b, x)
{
    if x == 0 {
        // Base case: exp(a, 0) = 1, exp(b, 0) = 1, exp(a*b, 0) = 1
    } else if a == 0 {
        // a == 0 and x > 0, then exp(0, x) = 0
        // exp(0, x) * exp(b, x) = 0 * exp(b, x) = 0
    } else if b == 0 {
        // b == 0 and x > 0, then exp(0, x) = 0
        // exp(a, x) * exp(0, x) = exp(a, x) * 0 = 0
    } else {
        ExpMulProof(a, b, x - 1);
        // exp(a, x-1) * exp(b, x-1) == exp(a * b, x-1)
        assert exp(a, x) == a * exp(a, x - 1);
        assert exp(b, x) == b * exp(b, x - 1);
        assert exp(a * b, x) == a * b * exp(a * b, x - 1);
    }
}