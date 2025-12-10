lemma {:induction false} FEqualsSum(n: nat, m: nat)
    ensures f(n, m) == n + m
{
    if n == 0 {
        // Base case: f(0, m) = m
    } else {
        FEqualsSum(n - 1, m);
        // f(n-1, m) = (n-1) + m
        // assert f(n - 1, m) == 1 + g(n - 1, m);
        GEqualsSum(n - 1, m);
        // g(n-1, m) = (n-1) + m
        assert  f(n - 1, m) == n - 1 + m;
        assert f(n, m) == 1 + (n - 1 + m);

    }
}

lemma {:induction false} GEqualsSum(n: nat, m: nat)
    ensures g(n, m) == n + m
{
    if m == 0 {
        // Base case: g(n, 0) = n
    } else {
        GEqualsSum(n, m - 1);
        // g(n, m-1) = (n) + m
        // assert g(n, m - 1) == 1 + f(n, m - 1);
        FEqualsSum(n, m - 1);
        // f(n, m-1) = (n) + m
        assert g(n, m - 1) == n + m - 1;
        assert g(n, m) == 1 + (n + m - 1);
    }
}