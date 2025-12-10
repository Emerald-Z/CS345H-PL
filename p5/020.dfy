// Bubble Sort

// Below is an implementation of bubble sort. You need to fill in three predicate functions
// to complete the program: two loop invariants and the `ensures` clause of Swap().
// Each function has a description, and there are stubs and TODOs for the predicates.

// I was able to complete each one of the predicates with about 2-3 clauses ANDed together, so they
// don't necessarily need to be overly complex (though you will probably need to use some `forall` terms).

// Recursively checks whether a list is sorted
predicate {:induction false} sorted(list: seq<int>)
{
    if |list| <= 1 then
        true
    else
        list[0] <= list[1] && sorted(list[1..])
}

// Checks whether two lists have the same set of elements (and length)
predicate {:induction false} sameList(list1: seq<int>, list2: seq<int>)
{
    |list1| == |list2| && multiset(list1) == multiset(list2)
}

// Swaps two elements in a list, returning the resulting list
// TODO: come up with an appropriate `ensures` term to fully describe what this function does
method {:induction false} Swap(listIn: seq<int>, i: nat, j: nat) returns (listOut: seq<int>)
    requires i <= j < |listIn|
    ensures sameList(listIn, listOut)
    ensures swapInvariant(listIn, listOut, i, j)
{
    listOut := listIn[i := listIn[j]][j := listIn[i]];
}

// Performs one round of a bubble sort, looping through the list and
// swapping out-of order elements until the largest one "bubbles" to the top
// TODO: come up with an appropriate loop invariant to describe this behavior
method {:induction false} RoundOfBubbling(listIn: seq<int>, i: nat) returns (listOut: seq<int>)
    requires 0 < i <= |listIn|
    requires outerLoopInvariant(listIn, i)

    ensures sameList(listIn, listOut)
    ensures outerLoopInvariant(listOut, i-1)
{
    listOut := listIn;
    var j: nat := 0;
    while (j + 1 < i)
        decreases i - (j + 1)
        invariant j + 1 <= i
        invariant sameList(listIn, listOut)
        invariant innerLoopInvariant(listIn, listOut, i, j)
        invariant outerLoopInvariant(listOut, i)
    {
        var next := j+1;
        if listOut[j] > listOut[next] {
            listOut := Swap(listOut, j, next);
        } else {}

        j := j+1;
    }
}

// Performs a bubble sort on the input list, repeatedly
// "bubbling" the largest element to the top with RoundOfBubbling()
// TODO: come up with an appropriate loop invariant
method {:induction false} BubbleSort(listIn: seq<int>) returns (listOut: seq<int>)
    ensures sameList(listIn, listOut)
    ensures sorted(listOut)
{
    listOut := listIn;
    var i: nat := |listIn|;
    while (i > 0)
        decreases i
        invariant sameList(listIn, listOut)
        invariant outerLoopInvariant(listOut, i)
    {
        listOut := RoundOfBubbling(listOut, i);
        i := i - 1;
    }
}

// Tests the bubble sort on a short list, printing the output
// method {:induction false} Main()
// {
//     var res := BubbleSort([4,2,3,1,5]);
//     print res;
// }


// Stubs:

// predicate {:induction false} swapInvariant(listIn: seq<int>, listOut: seq<int>, i: nat, j:nat)
//     requires i <= j < |listIn| == |listOut|
// {}

// predicate {:induction false} innerLoopInvariant(listIn: seq<int>, listOut: seq<int>, i: nat, j: nat)
//     requires j < i <= |listIn| == |listOut|
// {}

// predicate {:induction false} outerLoopInvariant(list: seq<int>, i: nat)
//     requires i <= |list|
// {}
