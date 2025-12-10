datatype MaxHeap = Null | Node(value: int, left: MaxHeap, right: MaxHeap)

function{:induction false} InsertMaxHeap(h: MaxHeap, x: int): MaxHeap
{
  match h
  {
    case Null => Node(x, Null, Null)
    // Flips sides to keep relative balance between trees
    case Node(v, l, r) =>
      if x > v then
        Node(x, InsertMaxHeap(r, v), l)
      else
        Node(v, InsertMaxHeap(r, x), l)
  }
}

function{:induction false} DeleteMaxHeap(h: MaxHeap): (int, MaxHeap)
  requires h != Null
{
  match h
  {
    case Node(v, l, r) =>
      if l == Null && r == Null then
        (v, Null)
      else if r == Null then
        (v, l)
      else if l == Null then
        (v, r)
      else 
        match (l, r)
        {
          case (Node(lv, ll, lr), Node(rv, rl, rr)) =>
            if lv >= rv then
              var (maxVal, newLeft) := DeleteMaxHeap(l);
              (v, Node(lv, newLeft, r))
            else
              var (maxVal, newRight) := DeleteMaxHeap(r);
              (v, Node(rv, l, newRight))
        }
  }
}


method{:induction false} TestInsertMaintainsMaxHeap(h: MaxHeap, x: int)
requires isMaxHeap(h)
{
    var newHeap := InsertMaxHeap(h, x);
    assert isMaxHeap(newHeap) by {insertionRetainsMaxHeap(h, x);}
}

method{:induction false} TestDeleteMaintainsMaxHeap(h: MaxHeap)
  requires isMaxHeap(h)
  requires h != Null
{
    var (maxVal, newHeap) := DeleteMaxHeap(h);
    assert isMaxHeap(newHeap) by {deletionRetainsMaxHeap(h);}
}


// Lemmas / Proof stubs:

// lemma{:induction false} {:verify true} deletionRetainsMaxHeap(h: MaxHeap)
//   requires isMaxHeap(h)
//   requires h != Null
//   ensures var (_, newHeap) := DeleteMaxHeap(h); isMaxHeap(newHeap) {}

// lemma{:induction false} {:verify true} insertionRetainsMaxHeap(h: MaxHeap, x: int) 
// requires isMaxHeap(h)
// ensures isMaxHeap(InsertMaxHeap(h, x)) {}

// predicate isMaxHeap(h: MaxHeap)