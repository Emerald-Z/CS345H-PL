// functions and predicates for gcd and divisibility
function {:induction false} gcd(a: nat, b: nat): nat
    decreases b
{
    if b == 0 then a else gcd(b,a % b)
}

predicate {:induction false} div(d: nat, n: nat)
{
    exists k: int :: n == d * k
}

predicate {:induction false} isGcd(d: nat, a: nat, b: nat)
{
    div(d, a) &&
    div(d, b) &&
    // Every common divisor of a and b also divides d.
    (forall e: nat :: div(e, a) && div(e, b) ==> div(e, d))
}

// I'm pretty sure you'll need all of these divisibility lemmas
// a|0
lemma {:induction false} div0(d: nat)
    ensures div(d, 0)
{
    assert 0 == d * 0;
}

// a|a
lemma {:induction false} divN(n: nat)
    ensures div(n, n)
{
    assert n == n * 1;
}

// d|a & d|b ==> d|(a % b)
lemma {:induction false} divMod(d: nat, a: nat, b: nat)
    requires b > 0
    requires div(d, a) && div(d, b)
    ensures div(d, a % b)
{
    var k1: int :| a == d * k1;
    var k2: int :| b == d * k2;

    calc {
        a % b;
        == a - (a / b) * b;
        == d * k1 - (a / b) * (d * k2);
        == d * k1 - d * ((a / b) * k2);
        == d * (k1 - (a / b) * k2);
    }
    assert div(d, a % b);
}

// d|a & d|(a % b) ==> d|a
lemma {:induction false} divR(d: nat, a: nat, b: nat)
    requires b > 0
    requires div(d, b) && div(d, a % b)
    ensures div(d, a)
{
    var k1: int :| b == d * k1;
    var k2: int :| a % b == d * k2;
    calc {
        a;
        == (a / b) * b + a % b;
        == (a / b) * (d * k1) + d * k2;
        == d * ((a / b) * k1) + d * k2;
        == d * ((a / b) * k1 + k2);
    }
    assert div(d, a); 
}

method {:induction false} enforceGcd(a: nat, b: nat)
    requires a > 0 || b > 0
    ensures isGcd(gcd(a, b), a, b)
{
    // show that gcd(a, b) is in fact the gcd of a and b
    assert isGcd(gcd(a, b), a, b) by {
        verifyGcd(a, b);
    }

    // show that gcd(a, b) == gcd(b, a)
    assert gcd(a, b) == gcd(b, a) by {
        gcdSymmetric(a, b);
    }

    // show that gcd(a, b) is unique
    if a > 0 || b > 0 {
        assert gcd(a, b) > 0 by {
            gcdNonZero(a, b);
        }

        // show that gcd(a, b) is maximal
        assert forall e: nat :: div(e, a) && div(e, b) ==> e <= gcd(a, b) by {
            forall e: nat 
                ensures div(e, a) && div(e, b) ==> e <= gcd(a, b)
            {
                if div(e, a) && div(e, b) {
                    gcdMaximal(e, a, b);
                }
            }
        }

        assert forall d1: nat, d2: nat :: 
            isGcd(d1, a, b) && isGcd(d2, a, b) ==> d1 == d2 by {
            forall d1: nat, d2: nat
                ensures isGcd(d1, a, b) && isGcd(d2, a, b) ==> d1 == d2
            {
                if isGcd(d1, a, b) && isGcd(d2, a, b) {
                    gcdUnique(d1, d2, a, b);
                }
            }
        }
    }
}

// I put a lot in this one, so here's some lemma stubs to help out
// ---------------------------------------------------------------
// //This lemma helped me, you may or may not need it
// lemma {:induction false} euclidStepPreservesIsGCD(a: nat, b: nat, d: nat)
//     requires b > 0
//     requires isGcd(d, b, a % b)
//     ensures isGcd(d, a, b)
// {

// }

// // gcd satisfies the isGCD predicate
// lemma {:induction false} verifyGcd(a: nat, b: nat)
//     ensures isGcd(gcd(a, b), a, b)
//     decreases b
// {

// }

// // gcd is non-zero if either a or b is non-zero
// lemma {:induction false} gcdNonZero(a: nat, b: nat)
//     requires a > 0 || b > 0
//     ensures gcd(a, b) > 0
//     decreases b
// {

// }

// // gcd is maximal
// // (techically gcd(0, 0) is undefined, but we disregard that edge case)
// lemma {:induction false} gcdMaximal(d: nat, a: nat, b: nat)
//     requires a > 0 || b > 0
//     requires div(d, a) && div(d, b)
//     ensures d <= gcd(a, b)
// {

// }

// // asserts gcd(a, b) == gcd(b, a)
// lemma {:induction false} gcdSymmetric(a: nat, b: nat)
//     ensures gcd(a, b) == gcd(b, a)
//     decreases b
// {

// }

// // asserts the uniqueness of the gcd
// // (if a or b is non-zero)
// lemma {:induction false} gcdUnique(d1: nat, d2: nat, a: nat, b: nat)
//     requires a > 0 || b > 0
//     requires isGcd(d1, a, b)
//     requires isGcd(d2, a, b)
//     ensures d1 == d2
// {

// }