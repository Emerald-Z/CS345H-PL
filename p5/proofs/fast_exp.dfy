lemma {:induction false} FastPowEqualsBasicPow(b: int, e: nat)
    ensures FastPow(b, e) == BasicPow(b, e)
{
    if e == 0 {
        // Base case: both return 1
    } else if e % 2 == 0 {
        // FastPow(b, e) = FastPow(b, e/2)^2
        FastPowEqualsBasicPow(b, e / 2);
        // induction gives FastPow(b, e/2) == BasicPow(b, e/2)

        BasicPowEven(b, e / 2);
        // BasicPow(b, e) == BasicPow(b, e/2) * BasicPow(b, e/2)
        
        assert FastPow(b, e) == FastPow(b, e/2) * FastPow(b, e/2);
        assert FastPow(b, e) == BasicPow(b, e/2) * BasicPow(b, e/2);
        assert FastPow(b, e) == BasicPow(b, e);
    } else {
        // FastPow(b, e) = FastPow(b, (e-1)/2)^2 * b
        // FastPow(b, (e-1)/2) = BasicPow(b, (e-1)/2)
        FastPowEqualsBasicPow(b, (e - 1) / 2);
        
        BasicPowOdd(b, (e - 1) / 2);
        // BasicPow(b, e) == BasicPow(b, (e-1)/2) * BasicPow(b, (e-1)/2) * b
        
        assert FastPow(b, e) == FastPow(b, (e-1)/2) * FastPow(b, (e-1)/2) * b;
        assert FastPow(b, e) == BasicPow(b, (e-1)/2) * BasicPow(b, (e-1)/2) * b;
        assert FastPow(b, e) == BasicPow(b, e);
    }
}

// BasicPow(b, 2k) = BasicPow(b, k)^2
lemma {:induction false} BasicPowEven(b: int, k: nat)
    ensures BasicPow(b, 2 * k) == BasicPow(b, k) * BasicPow(b, k)
    decreases k
{
    if k == 0 {
        // Base case: BasicPow(b, 0) = 1, so 1 == 1 * 1
    } else {
        BasicPowEven(b, k - 1);

        assert BasicPow(b, 2 * k) == b * BasicPow(b, 2 * k - 1);
        assert BasicPow(b, 2 * k - 1) == b * BasicPow(b, 2 * k - 2);
        assert BasicPow(b, 2 * k - 2) == BasicPow(b, 2 * (k - 1));
        assert BasicPow(b, 2 * k) == b * b * BasicPow(b, 2 * (k - 1));
        assert BasicPow(b, 2 * k) == b * b * BasicPow(b, k - 1) * BasicPow(b, k - 1);
        assert BasicPow(b, k) == b * BasicPow(b, k - 1);
        assert BasicPow(b, 2 * k) == BasicPow(b, k) * BasicPow(b, k);
    }
}

// BasicPow(b, 2k+1) = BasicPow(b, k)^2 * b
lemma {:induction false} BasicPowOdd(b: int, k: nat)
    ensures BasicPow(b, 2 * k + 1) == BasicPow(b, k) * BasicPow(b, k) * b
{
    // BasicPow(b, 2k+1) = b * BasicPow(b, 2k)

    BasicPowEven(b, k);
    assert BasicPow(b, 2 * k + 1) == b * BasicPow(b, 2 * k);
    assert BasicPow(b, 2 * k) == BasicPow(b, k) * BasicPow(b, k);
    assert BasicPow(b, 2 * k + 1) == BasicPow(b, k) * BasicPow(b, k) * b;
}
