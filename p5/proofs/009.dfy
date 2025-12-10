function {:induction false} Lemma0(): nat { 1 }

lemma {:induction false} Lemma1<T>(n : pos, l : seq<T>) 
    ensures |construct(n, l)| == n
{
    if |l| == 0 {
        // Base case: construct(n, []) = empty(n), and |empty(n)| = n
    } else {
        // construct(n, l) = insert(construct(n, l[1..]), l[0])
        Lemma1(n, l[1..]);
        // insert preserves the length of the sequence
        assert |insert(construct(n, l[1..]), l[0])| == |construct(n, l[1..])|;
    }
}

lemma {:induction false} Lemma2<T>(n : pos, l : seq<T>) 
    ensures forall t : T :: lookup(construct(n, l), t) == (t in l)
{
    if |l| == 0 {
        // Base case: empty list
        forall t : T
            ensures lookup(construct(n, l), t) == (t in l)
        {
            assert lookup(empty(n), t) == (t in []);
        }
    } else {
        // construct(n, l) = insert(construct(n, l[1..]), l[0])
        Lemma2(n, l[1..]);
        
        forall t : T
            ensures lookup(construct(n, l), t) == (t in l)
        {
            // insert preserves the lookup property
            InsertLookupLemma(construct(n, l[1..]), l[0], t);
            assert (t in l[1..]) || t == l[0] <==> (t in l);
        }
    }
}

lemma {:induction false} InsertLookupLemma<T>(s : seq<seq<T>>, a : T, t : T)
    requires |s| > 0
    ensures lookup(insert(s, a), t) == (lookup(s, t) || t == a)
{
    if hash(t, |s|) == hash(a, |s|) {
        // t and a hash to the same bucket
        assert insert(s, a)[hash(t, |s|)] == [a] + s[hash(a, |s|)];
        assert lookup(insert(s, a), t) == (t in ([a] + s[hash(a, |s|)]));
        assert (t in ([a] + s[hash(a, |s|)])) == ((t == a) || (t in s[hash(a, |s|)]));
        assert lookup(s, t) == (t in s[hash(t, |s|)]);
        assert hash(t, |s|) == hash(a, |s|);
        assert lookup(s, t) == (t in s[hash(a, |s|)]);
        assert lookup(insert(s, a), t) == ((t == a) || lookup(s, t));
    } else {
        // t and a hash to different buckets
        assert hash(t, |s|) != hash(a, |s|);
        assert insert(s, a)[hash(t, |s|)] == s[hash(t, |s|)];
        assert lookup(insert(s, a), t) == (t in s[hash(t, |s|)]);
        assert lookup(insert(s, a), t) == lookup(s, t);
        // If t == a, then hash(t, |s|) == hash(a, |s|) so t != a has to be true
        assert lookup(insert(s, a), t) == (lookup(s, t) || false);
        assert lookup(insert(s, a), t) == (lookup(s, t) || (t == a));
    }
}

lemma {:induction false} DeleteInsertLemma<T>(s : seq<seq<T>>, x : T, a : T, t : T)
    requires |s| > 0
    ensures lookup(delete(insert(s, x), a), t) == (lookup(delete(s, a), t) || (x == t && x != a))
{
    // delete and insert preserve length > 0
    assert |insert(s, x)| == |s|;
    assert |delete(s, a)| == |s|;
    assert |delete(insert(s, x), a)| == |insert(s, x)|;
    assert |insert(s, x)| > 0;
    assert |delete(s, a)| > 0;
    assert |delete(insert(s, x), a)| > 0;
    
    if x == a {
        // delete(insert(s, a), a) should equal s (if a wasn't in s) or delete(s, a) (if a was in s)
        // lookup(delete(insert(s, a), a), t) == lookup(s, t) when t != a
        var s_inserted := insert(s, x);
        var s_deleted := delete(s, a);
        var s_inserted_then_deleted := delete(s_inserted, a);
        
        DeleteLookupLemma(s_inserted, a, t);
        assert lookup(s_inserted_then_deleted, t) == (lookup(s_inserted, t) && t != a);
        InsertLookupLemma(s, x, t);
        assert lookup(s_inserted, t) == (lookup(s, t) || t == x);
        assert (lookup(s, t) || t == x) && t != a <==> lookup(s, t) && t != a;
        DeleteLookupLemma(s, a, t);
        assert lookup(s_deleted, t) == (lookup(s, t) && t != a);
        assert lookup(s_inserted_then_deleted, t) == lookup(s_deleted, t);
        assert lookup(s_inserted_then_deleted, t) == (lookup(s_deleted, t) || (x == t && x != a));
    } else {
        // x != a, so delete(insert(s, x), a) should equal insert(delete(s, a), x)
        var s_inserted := insert(s, x);
        var s_deleted := delete(s, a);
        var s_inserted_then_deleted := delete(s_inserted, a);
        
        DeleteLookupLemma(s_inserted, a, t);
        assert lookup(s_inserted_then_deleted, t) == (lookup(s_inserted, t) && t != a);
        InsertLookupLemma(s, x, t);
        assert lookup(s_inserted, t) == (lookup(s, t) || t == x);
        DeleteLookupLemma(s, a, t);
        assert lookup(s_deleted, t) == (lookup(s, t) && t != a);
        
        calc {
            lookup(s_inserted_then_deleted, t);
        ==
            lookup(s_inserted, t) && t != a;
        ==
            (lookup(s, t) || t == x) && t != a;
        ==
            (lookup(s, t) && t != a) || (t == x && t != a);
        ==
            lookup(s_deleted, t) || (x == t && x != a);
        }
    }
}

lemma {:induction false} Lemma3<T>(n : pos, l : seq<T>, a : T)
ensures forall t : T :: lookup(delete(construct(n, l), a), t) == (t in l && t != a)
{
    if |l| == 0 {
        // Base case: delete(construct(n, []), a) = construct(n, [])
        forall t : T
            ensures lookup(delete(construct(n, l), a), t) == (t in l && t != a)
        {
            assert delete(empty(n), a) == empty(n);
            assert lookup(empty(n), t) == false;
            assert !(t in []);
        }
    } else {
        Lemma3(n, l[1..], a);
        
        forall t : T
            ensures lookup(delete(construct(n, l), a), t) == (t in l && t != a)
        {
            if l[0] == a {
                DeleteInsertLemma(construct(n, l[1..]), l[0], a, t);
                assert (t in l[1..] && t != a) == (t in l && t != a);
            } else {
                DeleteInsertLemma(construct(n, l[1..]), l[0], a, t);
                assert (t in l[1..] && t != a) || (l[0] == t && l[0] != a) <==> (t in l && t != a);
            }
        }
    }
}

lemma {:induction false} Lemma4<T>(n : pos, l : seq<T>, a : T)
ensures forall t : T :: lookup(insert(construct(n, l), a), t) == (t in l || t == a)
{
    if |l| == 0 {
        // Base case: insert(construct(n, []), a) = construct(n, [a])
        forall t : T
            ensures lookup(insert(construct(n, l), a), t) == (t in l || t == a)
        {
            InsertLookupLemma(empty(n), a, t);
            assert lookup(insert(empty(n), a), t) == (lookup(empty(n), t) || t == a);
            assert lookup(empty(n), t) == false;
            assert (t in []) == false;
        }
    } else {
        Lemma4(n, l[1..], a);
        Lemma2(n, l);  // lookup(construct(n, l), t) == (t in l)
        
        forall t : T
            ensures lookup(insert(construct(n, l), a), t) == (t in l || t == a)
        {
            InsertLookupLemma(construct(n, l), a, t);
            assert (t in l) || t == a <==> (t in l || t == a);
        }
    }
}

lemma {:induction false} Lemma5<T>(n : pos, l : seq<T>, a : T)
requires a !in l
ensures forall t : T :: lookup(delete(insert(construct(n, l), a), a), t) == lookup(construct(n, l), t)
{
    var s := construct(n, l);
    Lemma2(n, l);  // lookup(s, t) == (t in l)
    forall t : T
        ensures lookup(delete(insert(s, a), a), t) == lookup(s, t)
    {
        DeleteInsertLemma(s, a, a, t);
        assert lookup(delete(insert(s, a), a), t) == (lookup(delete(s, a), t) || (a == t && a != a));
        assert (a == t && a != a) == false;
        assert lookup(delete(insert(s, a), a), t) == lookup(delete(s, a), t);
        DeleteLookupLemma(s, a, t);
        assert lookup(delete(s, a), t) == (lookup(s, t) && t != a);

        if t == a {
            assert lookup(s, a) == (a in l);  // by Lemma2
            assert a !in l;
            assert lookup(s, a) == false;
            assert lookup(delete(s, a), a) == (lookup(s, a) && a != a);
            assert lookup(delete(s, a), a) == false;
        } else {
            assert lookup(delete(s, a), t) == (lookup(s, t) && t != a);
            assert t != a;
            assert lookup(delete(s, a), t) == lookup(s, t);
        }
        assert lookup(delete(insert(s, a), a), t) == lookup(s, t);
    }
}

lemma {:induction false} FilterProperty<T>(l : seq<T>, a : T, t : T)
    ensures (t in filter(l, a)) == ((t in l) && t != a)
{
    // So t is in filter(l, a) if and only if t is in l and t != a
    if |l| == 0 {
        assert filter(l, a) == [];
        assert !(t in []);
        assert !(t in l);
    } else {
        if l[0] == a {
            // filter([a] + l[1..], a) = filter(l[1..], a)
            FilterProperty(l[1..], a, t);
            assert (t in l) == ((t == a) || (t in l[1..]));
            if t == a {
                assert !((t in l) && t != a);
            } else {
                assert (t in l) == (t in l[1..]);
            }
        } else {
            // filter([x] + l[1..], a) = [x] + filter(l[1..], a) where x != a
            FilterProperty(l[1..], a, t);
            if t == l[0] {
                assert t != a;
                assert ((t in l) && t != a) == true;
            } else {
                assert (t in l) == (t in l[1..]);
            }
        }
    }
}

lemma {:induction false} DeleteLookupLemma<T>(s : seq<seq<T>>, a : T, t : T)
    requires |s| > 0
    ensures lookup(delete(s, a), t) == (lookup(s, t) && t != a)
{
    if hash(t, |s|) == hash(a, |s|) {
        // t and a hash to the same bucket
        assert delete(s, a)[hash(t, |s|)] == filter(s[hash(t, |s|)], a);
        assert lookup(delete(s, a), t) == (t in filter(s[hash(t, |s|)], a));
        assert lookup(s, t) == (t in s[hash(t, |s|)]);
        FilterProperty(s[hash(t, |s|)], a, t);
        assert lookup(delete(s, a), t) == (lookup(s, t) && t != a);
    } else {
        // t and a hash to different buckets
        assert delete(s, a)[hash(t, |s|)] == s[hash(t, |s|)];
        assert lookup(delete(s, a), t) == (t in s[hash(t, |s|)]);
    }
}