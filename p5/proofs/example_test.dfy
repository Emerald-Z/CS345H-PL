// Proofs for example_test.dfy
// All lemmas must have {:induction false}

lemma {:induction false} Factorial_Positive(n: nat)
  ensures Factorial(n) > 0
{
  if n == 0 {
    // Base case: Factorial(0) = 1 > 0
  } else {
    // Inductive case: Factorial(n) = n * Factorial(n-1)
    // Since n > 0 and Factorial(n-1) > 0 (by induction), the product is > 0
    Factorial_Positive(n - 1);
  }
}

lemma {:induction false} Factorial_Grows(n: nat)
  requires n >= 1
  ensures Factorial(n + 1) > Factorial(n)
{
  // Factorial(n+1) = (n+1) * Factorial(n)
  assert Factorial(n + 1) == (n + 1) * Factorial(n);
  // We know n >= 1, so n+1 >= 2
  assert n + 1 >= 2;
  // We know Factorial(n) > 0 from Factorial_Positive
  Factorial_Positive(n);
  // Since n+1 >= 2 and Factorial(n) > 0, we have (n+1) * Factorial(n) >= 2 * Factorial(n) > Factorial(n)
  assert (n + 1) * Factorial(n) >= 2 * Factorial(n);
  assert 2 * Factorial(n) > Factorial(n);
}

lemma {:induction false} Factorial_Base()
  ensures Factorial(0) == 1
{
  // Direct from definition: Factorial(0) = 1
}

