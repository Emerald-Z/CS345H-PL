
method {:induction false} Selection_Sort(a: seq<int>) returns (b : seq<int>)
  ensures |b| == |a|
  ensures Sorted(b)
{
  if |a| == 0 {
    return []; 
  } else {
    var i := 0;
    var sorted := a;
    
    while (i < (|a| - 1))
      invariant 0 <= i < |a|
      invariant |sorted| == |a|
      invariant Outer_Loop_Invariant(sorted, i)
      invariant Permutation(a, sorted)
      decreases |a| - i
    {
      var min := i;
      var j := i + 1;
      
      while j < |a|
        invariant i <= min < |a|
        invariant i < j <= |a|
        invariant Inner_Loop_Invariant(sorted, min, i, j)
        invariant |sorted| == |a|
        decreases |a| - j
      {
        if (sorted[j] < sorted[min]) {
          min := j;
        }
        j := j + 1;
      }
      if (min != i) {
        var temp := sorted[i];
        sorted := sorted[i := sorted[min]][min := temp];
      }
      
      i := i + 1;
    }
    
    return sorted;
  }
}

