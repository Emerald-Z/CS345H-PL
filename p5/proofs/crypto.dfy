lemma {:induction false} XorBitCommutative(a: bool, b: bool)
    ensures XorBit(a, b) == XorBit(b, a)
{
    // definition
}

lemma {:induction false} XorBitAssociative(a: bool, b: bool, c: bool)
    ensures XorBit(XorBit(a, b), c) == XorBit(a, XorBit(b, c))
{

}

lemma {:induction false} XorBitIdentity(a: bool)
    ensures XorBit(a, a) == false
{

}

lemma {:induction false} XorBitInverse(a: bool, b: bool)
    ensures XorBit(XorBit(a, b), b) == a
{
    // If b is true, (a != true) != true is !a != true, which is a.
    // If b is false, (a != false) != false is a != false, which is a.
}

lemma {:induction false} XorSeqPreservesLength(a: seq<bool>, b: seq<bool>)
    requires |a| == |b|
    ensures |XorSeq(a, b)| == |a|
{
    if |a| > 0 {
        XorSeqPreservesLength(a[1..], b[1..]);
    }
}

lemma {:induction false} XorSeqCommutative(a: seq<bool>, b: seq<bool>)
    requires |a| == |b|
    ensures XorSeq(a, b) == XorSeq(b, a)
{
    if |a| > 0 {
        XorBitCommutative(a[0], b[0]);
        XorSeqCommutative(a[1..], b[1..]);
    }
}

lemma {:induction false} XorSeqAssociative(a: seq<bool>, b: seq<bool>, c: seq<bool>)
    requires |a| == |b| && |b| == |c|
    ensures |XorSeq(a, b)| == |c|
    ensures |XorSeq(b, c)| == |a|
    ensures XorSeq(XorSeq(a, b), c) == XorSeq(a, XorSeq(b, c))
{
    XorSeqPreservesLength(a, b);
    assert |XorSeq(a, b)| == |c|;
    XorSeqPreservesLength(b, c);
    assert |XorSeq(b, c)| == |a|;
    if |a| > 0 {
        XorBitAssociative(a[0], b[0], c[0]);
        XorSeqAssociative(a[1..], b[1..], c[1..]);
    }
}

lemma {:induction false} XorSeqIdentity(a: seq<bool>)
    ensures XorSeq(a, a) == Zeros(|a|)
{
    if |a| > 0 {
        XorBitIdentity(a[0]);
        XorSeqIdentity(a[1..]);
    }
}

lemma {:induction false} ZerosLength(n: nat)
    ensures |Zeros(n)| == n
{
    if n > 0 {
        ZerosLength(n - 1);
    }
}

lemma {:induction false} XorSeqZeroIdentity(n: nat, s: seq<bool>)
    requires n == |s|
    ensures |Zeros(n)| == |s|
    ensures XorSeq(Zeros(n), s) == s
{
    ZerosLength(n);
    assert |Zeros(n)| == |s|;
    if n > 0 {
        // XorBit(false, s[0]) == s[0]
        XorSeqZeroIdentity(n - 1, s[1..]);
    }
}

lemma {:induction false} XorSeqInverse(a: seq<bool>, b: seq<bool>)
    requires |a| == |b|
    ensures |XorSeq(a, b)| == |b|
    ensures XorSeq(XorSeq(a, b), b) == a
{
    XorSeqPreservesLength(a, b);
    assert |XorSeq(a, b)| == |b|;
    if |a| > 0 {
        XorBitInverse(a[0], b[0]);
        XorSeqInverse(a[1..], b[1..]);
    }
}

lemma {:induction false} OtpEncryptPreservesLength(m: seq<bool>, k: seq<bool>)
    requires |m| == |k|
    ensures |OtpEncrypt(m, k)| == |m|
{
    XorSeqPreservesLength(m, k);
}

lemma {:induction false} OtpCiphertextKeyLength(m: seq<bool>, k: seq<bool>)
    requires |m| == |k|
    ensures |OtpEncrypt(m, k)| == |k|
{
    XorSeqPreservesLength(m, k);
}

lemma {:induction false} OtpDecryptPreservesLength(c: seq<bool>, k: seq<bool>)
    requires |c| == |k|
    ensures |OtpDecrypt(c, k)| == |c|
{
    XorSeqPreservesLength(c, k);
}

lemma {:induction false} OtpEncryptDecryptCorrectness(m: seq<bool>, k: seq<bool>)
    requires |m| == |k|
    ensures |OtpEncrypt(m, k)| == |k|
    ensures OtpDecrypt(OtpEncrypt(m, k), k) == m
{
    OtpEncryptPreservesLength(m, k);
    assert |OtpEncrypt(m, k)| == |k|;
    // OtpDecrypt(OtpEncrypt(m, k), k) = XorSeq(XorSeq(m, k), k)
    XorSeqInverse(m, k);
}

lemma {:induction false} OtpDoubleEncryptIdentity(m: seq<bool>, k: seq<bool>)
    requires |m| == |k|
    ensures |OtpEncrypt(m, k)| == |k|
    ensures OtpEncrypt(OtpEncrypt(m, k), k) == m
{
    OtpEncryptPreservesLength(m, k);
    assert |OtpEncrypt(m, k)| == |k|;
    // OtpEncrypt(OtpEncrypt(m, k), k) = XorSeq(XorSeq(m, k), k)
    XorSeqInverse(m, k);
}

lemma {:induction false} OtpEncryptCommutative(m: seq<bool>, k1: seq<bool>, k2: seq<bool>)
    requires |m| == |k1| && |k1| == |k2|
    ensures |OtpEncrypt(m, k1)| == |k2|
    ensures |OtpEncrypt(m, k2)| == |k1|
    ensures OtpEncrypt(OtpEncrypt(m, k1), k2) == OtpEncrypt(OtpEncrypt(m, k2), k1)
{
    OtpEncryptPreservesLength(m, k1);
    assert |OtpEncrypt(m, k1)| == |k2|;
    OtpEncryptPreservesLength(m, k2);
    assert |OtpEncrypt(m, k2)| == |k1|;
    // XorSeq(XorSeq(m, k1), k2) = XorSeq(m, XorSeq(k1, k2))
    XorSeqAssociative(m, k1, k2);
    // XorSeq(k1, k2) = XorSeq(k2, k1)
    XorSeqCommutative(k1, k2);
    // XorSeq(m, XorSeq(k2, k1)) = XorSeq(XorSeq(m, k2), k1)
    XorSeqAssociative(m, k2, k1);
}

lemma {:induction false} OtpCombinedKeyEncryption(m: seq<bool>, k1: seq<bool>, k2: seq<bool>)
    requires |m| == |k1| && |k1| == |k2|
    ensures |XorSeq(k1, k2)| == |m|
    ensures |OtpEncrypt(m, k1)| == |k2|
    ensures OtpEncrypt(m, XorSeq(k1, k2)) == OtpEncrypt(OtpEncrypt(m, k1), k2)
{
    XorSeqPreservesLength(k1, k2);
    assert |XorSeq(k1, k2)| == |m|;
    OtpEncryptPreservesLength(m, k1);
    assert |OtpEncrypt(m, k1)| == |m|;
    assert |OtpEncrypt(m, k1)| == |k2|;
    XorSeqAssociative(m, k1, k2);
    assert XorSeq(m, XorSeq(k1, k2)) == XorSeq(XorSeq(m, k1), k2);
    assert OtpEncrypt(m, XorSeq(k1, k2)) == XorSeq(m, XorSeq(k1, k2));
    assert OtpEncrypt(OtpEncrypt(m, k1), k2) == XorSeq(XorSeq(m, k1), k2);
}

lemma {:induction false} KeyForSound(m: seq<bool>, c: seq<bool>)
    requires |m| == |c|
    ensures |KeyFor(m, c)| == |m|
    ensures OtpEncrypt(m, KeyFor(m, c)) == c
{
    XorSeqPreservesLength(m, c);
    assert |KeyFor(m, c)| == |m|;
    OtpEncryptPreservesLength(m, KeyFor(m, c));
    XorSeqAssociative(m, m, c);
    // XorSeq(XorSeq(m, m), c) == XorSeq(Zeros(|m|), c) 
    XorSeqIdentity(m);
    // XorSeq(Zeros(|m|), c) == c
    XorSeqZeroIdentity(|m|, c);
    assert XorSeq(m, XorSeq(m, c)) == c;
    assert OtpEncrypt(m, KeyFor(m, c)) == XorSeq(m, KeyFor(m, c));
    assert KeyFor(m, c) == XorSeq(m, c);
    assert OtpEncrypt(m, KeyFor(m, c)) == c;
}

lemma {:induction false} KeyForUnique(m: seq<bool>, c: seq<bool>, k: seq<bool>)
    requires |m| == |k| && |m| == |c|
    requires IsOtpCipher(m, k, c) // c == XorSeq(m, k)
    ensures k == KeyFor(m, c) // KeyFor(m, c) == XorSeq(m, c)
{
    XorSeqAssociative(m, m, k);
    XorSeqIdentity(m);
    XorSeqZeroIdentity(|m|, k);
}
