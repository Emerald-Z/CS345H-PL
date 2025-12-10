lemma {:induction false} BinarySearch_ValidIndex(a: seq<int>, x: int)
  requires Sorted(a)
  ensures var result := BinarySearch(a, x); result == -1 || (0 <= result < |a|)
  decreases |a|
{
  if |a| == 0 {
  } else if |a| == 1 {
    // Single element: returns 0 if found (0 < 1), -1 if not
    if a[0] == x {
      assert BinarySearch(a, x) == 0;
      assert 0 < |a|;
    } else {
      assert BinarySearch(a, x) == -1;
    }
  } else {
    var mid := |a| / 2;
    if a[mid] == x {
      // found mid
      assert BinarySearch(a, x) == mid;
      assert 0 <= mid < |a|;
    } else if a[mid] < x {
      // right half search|a[mid+1..]| < |a| since mid+1 > 0
      assert |a[mid + 1..]| < |a|;
      BinarySearch_ValidIndex(a[mid + 1..], x);
    } else {
      // left half search |a[..mid]| < |a| since mid < |a| when |a| > 1
      assert |a[..mid]| < |a|;
      BinarySearch_ValidIndex(a[..mid], x);
    }
  }
}

// If binary search returns -1, the element is not in the sequence
lemma {:induction false} BinarySearch_NotFound(a: seq<int>, x: int)
  requires Sorted(a)
  ensures var result := BinarySearch(a, x); result == -1 ==> x !in a
  decreases |a|
{
  if |a| == 0 {
    // empty sequence: -1 is correct, x is not in empty sequence
    assert x !in a;
  } else if |a| == 1 {
    // single element: if not found, x != a[0], so x !in a
    if a[0] != x {
      assert BinarySearch(a, x) == -1;
      assert x !in a;
    }
  } else {
    var mid := |a| / 2;
    if a[mid] == x {
      // found: won't return -1
    } else if a[mid] < x {
      assert |a[mid + 1..]| < |a|;
      BinarySearch_NotFound(a[mid + 1..], x);
      if BinarySearch(a[mid + 1..], x) == -1 {
        assert x !in a[mid + 1..];
        // all elements in a[..mid+1] are <= a[mid] < x
        assert forall i :: 0 <= i <= mid ==> a[i] <= a[mid] < x;
        assert x !in a;
      }
    } else {
      assert |a[..mid]| < |a|;
      BinarySearch_NotFound(a[..mid], x);
      if BinarySearch(a[..mid], x) == -1 {
        assert x !in a[..mid];
        // all elements in a[mid..] are >= a[mid] > x
        assert forall i :: mid <= i < |a| ==> a[i] >= a[mid] > x;
        assert x !in a;
      }
    }
  }
}

// If element is found at midpoint, returns correct index
lemma {:induction false} BinarySearch_Midpoint(a: seq<int>, x: int)
  requires Sorted(a)
  requires |a| > 0
  requires a[|a|/2] == x
  ensures var result := BinarySearch(a, x); result == |a|/2 && result < |a| && a[result] == x
{
  var mid := |a| / 2;
  assert BinarySearch(a, x) == mid;
  // mid is always < |a| when |a| > 0
  assert mid < |a|;
  // a[mid] == x by assumption
  assert a[mid] == x;
}

