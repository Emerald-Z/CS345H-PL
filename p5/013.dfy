function {:induction false} Factorial(n: nat): nat
  decreases n
{
  if n == 0 then 1 else n * Factorial(n - 1)
}

method {:induction false} FactorialTest(n: nat)
{
  assert Factorial(n) >= 1 by {
    FactorialBounds(n);
  }

  assert n > 0 ==> Factorial(n) >= n by {
    FactorialBounds(n);
  }
}
