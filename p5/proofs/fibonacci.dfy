// IterativeFibHelper(n, a, b, i) = fib(n)
// know that a = fib(i) and b = fib(i+1)
lemma {:induction false} FibHelper(n: nat, a: nat, b: nat, i: nat)
    requires a == RecFib(i) && b == RecFib(i + 1) && i <= n
    ensures IterativeFibHelper(n, a, b, i) == RecFib(n)
    decreases n - i
{
    if i >= n {
        // Base case: i == n so a = fib(i) = fib(n)
    } else {
        FibHelper(n, b, a + b, i + 1);
    }
}

lemma {:induction false} IterEqualsRec(n: nat)
    ensures IterFib(n) == RecFib(n)
{
    FibHelper(n, 0, 1, 0);
}
