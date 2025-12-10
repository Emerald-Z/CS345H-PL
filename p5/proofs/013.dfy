lemma {:induction false} FactorialBounds(n: nat) 
    requires n >= 0
    ensures Factorial(n) >= 1
{
    if n == 0 {
        assert Factorial(0) == 1;
        assert Factorial(0) >= 1;
    } else {
        FactorialBounds(n-1);
        assert Factorial(n) == n * Factorial(n-1);
        assert n > 0 ==> Factorial(n) >= n;
    }
}
