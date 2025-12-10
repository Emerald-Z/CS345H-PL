// Proving properties of a factorial function
function {:induction false} Factorial(n: nat): nat
  decreases n
{
  if n == 0 then 1 else n * Factorial(n - 1)
}

method Test_Factorial_Positive(n: nat)
{
  assert Factorial(n) > 0 by {
    Factorial_Positive(n);
  }
}

// Factorial(n+1) > Factorial(n) for n >= 1
method Test_Factorial_Grows(n: nat)
  requires n >= 1
{
  assert Factorial(n + 1) > Factorial(n) by {
    Factorial_Grows(n);
  }
}

// factorial of 0 is 1
method Test_Factorial_Base()
{
  assert Factorial(0) == 1 by {
    Factorial_Base();
  }
}

