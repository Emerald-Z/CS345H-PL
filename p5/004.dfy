predicate {:induction false} Sorted(s: seq<int>) {
  forall i, j :: (0 <= i < j < |s|) ==> s[i] <= s[j]
}
function {:induction false} InsertSort(l: seq<int>): seq<int>
  decreases |l|
{
  if |l| == 0 then l
  else Insert(l[0], InsertSort(l[1..]))
}

function {:induction false} Insert(x: int, s: seq<int>): seq<int>
  decreases |s|
{
  if |s| == 0 then [x]
  else if x <= s[0] then [x] + s
  else [s[0]] + Insert(x, s[1..])
}

method {:induction false} InsertSortTest(l: seq<int>) {
  var sorted := InsertSort(l);
  assert Sorted(sorted) by {
    proof(l);
  }

}