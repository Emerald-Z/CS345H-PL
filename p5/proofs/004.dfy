// Helper lemma: Insert preserves sortedness
// If s is sorted, then Insert(x, s) is also sorted
lemma {:induction false} Insert_Preserves_Sorted(x: int, s: seq<int>)
    requires Sorted(s)
    ensures Sorted(Insert(x, s))
{
    if |s| == 0 {
    } else if x <= s[0] {
        // Case: x <= s[0], so Insert(x, s) = [x] + s
    } else {
        // Case: x > s[0], so Insert(x, s) = [s[0]] + Insert(x, s[1..])
        // s[1..] is also sorted
        assert Sorted(s[1..]);
        // Apply induction: Insert(x, s[1..]) is sorted
        Insert_Preserves_Sorted(x, s[1..]);
        // show [s[0]] + Insert(x, s[1..]) is sorted
        // if |s[1..]| > 0, then s[0] <= s[1] (since s is sorted)
        // The first element of Insert(x, s[1..]) is either:
        //   - x (if s[1..] is empty or x <= s[1])
        //   - s[1] (if x > s[1])
        // In all cases, s[0] <= first element of Insert(x, s[1..])
        assert |Insert(x, s[1..])| > 0;
        var first := Insert(x, s[1..])[0];
        if |s[1..]| == 0 {
            assert first == x;
            assert s[0] < x;  // since x > s[0]
        } else if x <= s[1] {
            assert first == x;
            assert s[0] < x;  // since x > s[0]
        } else {
            assert first == s[1];
            assert s[0] <= s[1]; 
        }
    }
}

lemma {:induction false} proof(l: seq<int>)
    ensures Sorted(InsertSort(l))
{
    if |l| == 0 {
        // Base case: empty list is sorted
    } else {
        proof(l[1..]);
        Insert_Preserves_Sorted(l[0], InsertSort(l[1..]));
        assert InsertSort(l) == Insert(l[0], InsertSort(l[1..]));
        assert Sorted(InsertSort(l));
    }
}