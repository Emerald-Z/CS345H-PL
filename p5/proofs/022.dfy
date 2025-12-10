predicate isMaxHeap(h: MaxHeap)
{
    match h {
        case Null => true
        case Node(v, l, r) =>
            isMaxHeap(l) &&
            isMaxHeap(r) &&
            (match l {
                case Null => true
                case Node(lv, _, _) => v >= lv
            }) &&
            (match r {
                case Null => true
                case Node(rv, _, _) => v >= rv
            })
    }
}

lemma{:induction false} {:verify true} insertionRetainsMaxHeap(h: MaxHeap, x: int) 
    requires isMaxHeap(h)
    ensures isMaxHeap(InsertMaxHeap(h, x))
{
    match h {
        case Null => {
            // Base case: InsertMaxHeap(Null, x) = Node(x, Null, Null)
            // Both children are Null (which are max heaps), so this is a max heap
        }
        case Node(v, l, r) => {
            if x > v {
                // InsertMaxHeap(h, x) = Node(x, InsertMaxHeap(r, v), l)
                insertionRetainsMaxHeap(r, v);
            } else {
                // InsertMaxHeap(h, x) = Node(v, InsertMaxHeap(r, x), l)
                insertionRetainsMaxHeap(r, x);
            }
        }
    }
}

lemma{:induction false} {:verify true} deletionRetainsMaxHeap(h: MaxHeap)
    requires isMaxHeap(h)
    requires h != Null
    ensures var (_, newHeap) := DeleteMaxHeap(h); isMaxHeap(newHeap)
{
    match h {
        case Node(v, l, r) => {
            if l == Null && r == Null {
                // DeleteMaxHeap(h) = (v, Null)
            } else if r == Null {
                // DeleteMaxHeap(h) = (v, l)
                // l is already a max heap (from isMaxHeap(h))
            } else if l == Null {
                // DeleteMaxHeap(h) = (v, r)
                // r is already a max heap (from isMaxHeap(h))
            } else {
                match (l, r) {
                    case (Node(lv, ll, lr), Node(rv, rl, rr)) => {
                        if lv >= rv {
                            // DeleteMaxHeap(h) = (v, Node(lv, newLeft, r))
                            // where (maxVal, newLeft) = DeleteMaxHeap(l)
                            deletionRetainsMaxHeap(l);
                        } else {
                            // DeleteMaxHeap(h) = (v, Node(rv, l, newRight))
                            // where (maxVal, newRight) = DeleteMaxHeap(r)
                            deletionRetainsMaxHeap(r);
                        }
                    }
                }
            }
        }
    }
}
