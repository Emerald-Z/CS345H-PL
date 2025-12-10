/* 
This test case provides a functional implementation of a hash set.
Your job is to verify some fundamental correctness properties of this implementation.
I asked ChatGPT to show examples for concepts like proving foralls and defining axioms.
However, I did not use Copilot or any other code or text generation tool.
*/

// used for constraining the sizes of the underlying containers of the sets
type pos = n : nat | n > 0 witness Lemma0() // Dafny is too dumb to figure this out on its own

// we want the hash set to work for any valid hash function 
// hence, we avoid defining it and instead ensure its properties axiomatically
function hash<T>(x : T, n : pos): nat
ensures {:induction false} {:axiom} hash(x, n) < n

// construct an empty hash set
function {:induction false} empty<T>(n : pos): seq<seq<T>>
{
    seq(n, i => [])
}

// helper method for deleting items from (entries in a) set
function {:induction false} filter<T(==)>(l : seq<T>, t : T): seq<T>
{
    if |l| == 0 then [] else if l[0] == t then filter(l[1..], t) else [l[0]] + filter(l[1..], t)
}

// removes all items equal to t from the set s (so looking up t in s should give false)
function {:induction false} delete<T(==)>(s : seq<seq<T>>, t : T): seq<seq<T>>
requires |s| > 0
{
    s[..hash(t, |s|)] + [filter(s[hash(t, |s|)], t)] + s[hash(t, |s|)+1..]
}

// inserts an item t into the set s (so looking up t in s should give true)
function {:induction false} insert<T>(s : seq<seq<T>>, t : T): seq<seq<T>>
requires |s| > 0
{
    s[..hash(t, |s|)] + [([t] + s[hash(t, |s|)])] + s[hash(t, |s|)+1..]
}

// constructs a set from a list of items for the set to initially contain
function {:induction false} construct<T>(n : pos, l : seq<T>): seq<seq<T>>
{
    if |l| == 0 then empty(n) else insert(construct(n, l[1..]), l[0])
}

// checks whether an item t is in a set s
function {:induction false} lookup<T(==)>(s : seq<seq<T>>, t : T): bool
// runtime: hash + sequence indexing (should be O(1)) + |s[hash(t, |s|)]|
// with a good (evenly distributing) hash function, |s[hash(t, |s|)]| grows inversely with n
// good enough hash functions should be able to run in about O(log(n))
// hence, lookup in this should run a lot faster than traditional list lookup
requires |s| > 0
{
    t in (s[hash(t, |s|)]) 
}

// a variety of checks for verifying the correctness of this set implementation
method {:induction false} Correct<T(==)>(n : pos, l : seq<T>, a : T)
{
    // empty set constructor is correct
    var e : seq<seq<T>> := empty(n);
     // Dafny/z3 can solve these without help
    assert |e| == n; // correct size (type) set
    assert forall t : T :: !lookup(e, t); // empty set is in fact empty

    // list-based constructor is correct
    var s : seq<seq<T>> := construct(n, l);
    assert |s| == n by {
        // ensures the constructor makes a set of the appropriate size (dependent type)
        Lemma1(n, l);
    }
    assert forall t : T :: lookup(s, t) == (t in l) by {
        // reduces hash set correctness to list set correctness
        // since sequence set correctness is a Dafny builtin, we will assume it works
        Lemma2(n, l); 
    }

    // deletion in newly constructed map is correct
    assert forall t : T :: lookup(delete(s, a), t) == (t in l && t != a) by {
        Lemma3(n, l, a); 
    }

    // insertion into newly created map is correct
    assert forall t : T :: lookup(insert(s, a), t) == (t in l || t == a) by {
        Lemma4(n, l, a);
    }

    // inserting, then deleting, an absent element yields the original set
    if (a !in l) {
        assert forall t : T :: lookup(delete(insert(s, a), a), t) == lookup(s, t) by {
            Lemma5(n, l, a);
        }
    }
}

/*
lemma stubs for the convenience of the prover
these do not provide any hints beyond what is already in Correct()
they merely require the constraints on the assertion and ensure the body of the assertion
*/

// function {:induction false} Lemma0(): nat
// {
// }

// lemma {:induction false} Lemma1<T>(n : pos, l : seq<T>) 
// ensures |construct(n, l)| == n
// {
// }

// lemma {:induction false} Lemma2<T>(n : pos, l : seq<T>) 
// ensures forall t : T :: lookup(construct(n, l), t) == (t in l)
// {
// }

// lemma {:induction false} Lemma3<T>(n : pos, l : seq<T>, a : T)
// ensures forall t : T :: lookup(delete(construct(n, l), a), t) == (t in l && t != a)
// {
// }

// lemma {:induction false} Lemma4<T>(n : pos, l : seq<T>, a : T)
// ensures forall t : T :: lookup(insert(construct(n, l), a), t) == (t in l || t == a)
// {
// }

// lemma {:induction false} Lemma5<T>(n : pos, l : seq<T>, a : T)
// requires a !in l
// ensures forall t : T :: lookup(delete(insert(construct(n, l), a), a), t) == lookup(construct(n, l), t)
// {
// }