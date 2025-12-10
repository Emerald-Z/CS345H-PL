lemma {:induction false} FoldRightAddLemma(lst: seq<int>, x: int, acc: int)
    ensures fold_right((a, b) => a + b, lst, x + acc) == x + fold_right((a, b) => a + b, lst, acc)
    decreases |lst|
{
    if |lst| == 0 {
        // Base case: both sides equal x + acc
    } else {
        FoldRightAddLemma(lst[1..], x, acc);
    }
}

lemma {:induction false} AddAllProof(lst: seq<int>, acc: int)
    requires |lst| >= 0
    ensures add_all_fold(lst, acc) == add_all_recursive(lst, acc)
{
    if |lst| == 0 {
        // Base case
    } else {
        AddAllProof(lst[1..], acc + lst[0]);

        FoldRightAddLemma(lst[1..], lst[0], acc);
        
        assert add_all_fold(lst, acc) == lst[0] + add_all_fold(lst[1..], acc);
        assert lst[0] + add_all_fold(lst[1..], acc) == add_all_fold(lst[1..], acc + lst[0]);
        assert add_all_fold(lst[1..], acc + lst[0]) == add_all_recursive(lst[1..], acc + lst[0]);
        assert add_all_recursive(lst[1..], acc + lst[0]) == add_all_recursive(lst, acc);
    }
}
