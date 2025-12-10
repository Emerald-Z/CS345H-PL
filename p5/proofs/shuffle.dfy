lemma SwapIsPermutation<T(!new)>(s: seq<T>, i: nat, j: nat)
  requires i < |s| && j < |s|
  ensures IsPermutation(s, Swap(s, i, j))
{
  assert |s| == |Swap(s, i, j)|;
  
  forall x | true
    ensures Count(s, x) == Count(Swap(s, i, j), x)
  {
    SwapPreservesCount(s, i, j, x);
  }
}

lemma {:induction false} SwapPreservesCount<T(!new)>(s: seq<T>, i: nat, j: nat, x: T)
  requires i < |s| && j < |s|
  ensures Count(s, x) == Count(Swap(s, i, j), x)
{
  if i == j {
    assert Swap(s, i, j) == s;
  } else {
    var swapped := Swap(s, i, j);
    assert swapped[i] == s[j];
    assert swapped[j] == s[i]; // swap was valid
    
    if |s| == 0 {
    } else if 0 == i {
      if j == 0 {
        assert false;
      } else {
        SwapFirstWithPos(s, j, x); // first element swap preserves count of any element
      }
    } else if 0 == j {
      SwapFirstWithPos(s, i, x);
    } else {
      assert s[0] == swapped[0];
      var s_rest := s[1..];
      var swapped_rest := swapped[1..];
      SwapPreservesCount(s_rest, i-1, j-1, x); // swapping preserves count of any element
      assert Count(s, x) == (if s[0] == x then 1 else 0) + Count(s_rest, x);
      assert Count(swapped, x) == (if swapped[0] == x then 1 else 0) + Count(swapped_rest, x);
      assert Count(s, x) == Count(swapped, x);
    }
  }
}

lemma {:induction false} SwapFirstWithPos<T(!new)>(s: seq<T>, pos: nat, x: T)
  requires 0 < pos < |s|
  ensures Count(s, x) == Count(Swap(s, 0, pos), x)
{
  var swapped := Swap(s, 0, pos);
  assert swapped[0] == s[pos];
  assert swapped[pos] == s[0];
  
  if |s| <= 1 {
    assert false;
  } else if pos == 1 {
    var s_rest := s[1..];
    var swapped_rest := swapped[1..];
    assert swapped_rest[0] == s[0];
    assert s_rest[0] == s[1];
    assert s_rest[1..] == swapped_rest[1..];
    
    calc {
      Count(s, x);
    ==
      (if s[0] == x then 1 else 0) + Count(s_rest, x);
    ==
      (if s[0] == x then 1 else 0) + (if s[1] == x then 1 else 0) + Count(s_rest[1..], x);
    ==
      (if s[1] == x then 1 else 0) + (if s[0] == x then 1 else 0) + Count(swapped_rest[1..], x);
    ==
      (if swapped[0] == x then 1 else 0) + (if s[0] == x then 1 else 0) + Count(swapped_rest[1..], x);
    ==
      (if swapped[0] == x then 1 else 0) + Count(swapped_rest, x);
    ==
      Count(swapped, x);
    }
  } else {
    var s_rest := s[1..];
    var swapped_rest := swapped[1..];
    assert swapped_rest[pos-1] == s[0];
    assert s_rest[pos-1] == s[pos];
    assert forall k :: 0 <= k < |s_rest| && k != pos-1 ==> s_rest[k] == swapped_rest[k];
    
    // Prove that Count(s_rest, x) and Count(swapped_rest, x) differ only by the swap at position pos-1
    SeqDifferByOne(s_rest, swapped_rest, pos-1, s[pos], s[0], x);
    
    calc {
      Count(s, x);
    ==
      (if s[0] == x then 1 else 0) + Count(s_rest, x);
    ==
      (if s[0] == x then 1 else 0) + Count(swapped_rest, x) - (if s[0] == x then 1 else 0) + (if s[pos] == x then 1 else 0);
    ==
      Count(swapped_rest, x) + (if s[pos] == x then 1 else 0);
    ==
      Count(swapped_rest, x) + (if swapped[0] == x then 1 else 0);
    ==
      (if swapped[0] == x then 1 else 0) + Count(swapped_rest, x);
    ==
      Count(swapped, x);
    }
  }
}

lemma {:induction false} SeqDifferByOne<T(!new)>(s: seq<T>, t: seq<T>, pos: nat, oldVal: T, newVal: T, x: T)
  requires |s| == |t| && pos < |s| && t[pos] == newVal && s[pos] == oldVal
  requires forall k :: 0 <= k < |s| && k != pos ==> s[k] == t[k]
  ensures Count(t, x) == Count(s, x) - (if oldVal == x then 1 else 0) + (if newVal == x then 1 else 0)
  decreases |s|
{
  if |s| == 0 {
    assert false; // contradicts pos < |s|
  } else if pos == 0 {
    assert s[0] == oldVal;
    assert t[0] == newVal;
    assert s[1..] == t[1..];
  } else {
    assert s[0] == t[0];
    SeqDifferByOne(s[1..], t[1..], pos-1, oldVal, newVal, x);
  }
}
