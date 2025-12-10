lemma {:induction false} TransitiveDivide(p: nat, k: nat, n: nat)
    requires Divides(p, k) && Divides(k, n)
    ensures Divides(p, n)
{
    // p * a == k
    var a: nat :| p * a == k;
    // k * b == n
    var b: nat :| k * b == n;
    // n == k * b == (p * a) * b == p * (a * b)
    assert n == p * (a * b);
    assert Divides(p, n);
}

lemma {:induction false} PrimeDivisorLemma(n: nat)
    requires n > 1
    ensures exists p :: Prime(p) && Divides(p, n)
{
    if Prime(n) {
        // Base case: n is prime
        assert n * 1 == n;
        assert Divides(n, n);
    } else {
        // n is not prime - find divisor
        var k: nat :| 1 < k < n && Divides(k, n); // such that k div n
        
        PrimeDivisorLemma(k);
        // exists p :: Prime(p) && Divides(p, k)
        
        // show k we found divides n
        // p divides k from lemma so use transitivity p divides n
        var p: nat :| Prime(p) && Divides(p, k);
        TransitiveDivide(p, k, n);
        assert Divides(p, n);
    }
}
