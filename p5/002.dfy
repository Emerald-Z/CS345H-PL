// You will definitely find this useful:
// proves that the computed (a) satisfies the formal
// maximum-subarray specification IsMaxSubSum(a, MaxSubarray(a))
// lemma {:induction false} MaxSubarrayIsMaximum(a: array<int>)
//     ensures IsMaxSubSum(a, MaxSubarray(a))
// {
// }

// proves that when all array elements are non-negative,
// the maximum subarray is exactly the full prefix of the array
// lemma {:induction false} AllNonNegativeFullSum(a: array<int>)
//     requires a.Length > 0
//     requires forall k :: 0 <= k < a.Length ==> a[k] >= 0
//     ensures MaxSubarray(a) == Sum(a, 0, a.Length - 1)
// {
// }

// proves that when all array elements are negative,
// the maximum subarray is the single least-negative element
// lemma {:induction false} AllNegativeChoosesMax(a: array<int>)
//     requires a.Length > 0
//     requires forall k :: 0 <= k < a.Length ==> a[k] < 0
//     ensures MaxSubarray(a) == MaxElement(a)
// {
// }

// proves that the shifted variant ShiftedMaxSubarray(a, c)
// satisfies the formal shifted-maximum-subarray specification
// lemma {:induction false} ShiftedMaxLemma(a: array<int>, c: int)
//     ensures IsShiftedMaxSubSum(a, c, ShiftedMaxSubarray(a, c))
// {
// }

// And now, for the fun bit!
// We do the Kadane's algorithm correctness (maximum contiguous subarray sum)
// For us, if all array is negative, we return the least negative element

// Computes sum of subarray [s..t] where each element contributes an additional constant c.
function {:induction false} ShiftedSum(a: array<int>, c: int, s: int, t: int): int
    requires 0 <= s
    requires t < a.Length
    ensures s > t ==> ShiftedSum(a, c, s, t) == 0
    reads a
    decreases t - s + 1
{
    if s > t then 0 else a[s] + c + ShiftedSum(a, c, s + 1, t)
}

// Specification: value is the maximum shifted-sum over all contiguous subarrays.
predicate {:induction false} IsShiftedMaxSubSum(a: array<int>, c: int, value: int)
    reads a
{
    (a.Length == 0 && value == 0) ||
    (a.Length > 0 &&
        (exists s, t :: 0 <= s <= t < a.Length && value == ShiftedSum(a, c, s, t)) &&
        (forall s, t :: 0 <= s <= t < a.Length ==> ShiftedSum(a, c, s, t) <= value))
}

function {:induction false} Sum(a: array<int>, i: int, j: int): int
    requires 0 <= i
    requires j < a.Length
    ensures i > j ==> Sum(a, i, j) == 0
    reads a
    decreases j - i + 1
{
    if i > j then 0 else a[i] + Sum(a, i + 1, j)
}

// The maximum sum of any subarray ending exactly at index idx.
function {:induction false} MaxEnding(a: array<int>, idx: int): int
    requires 0 <= idx < a.Length
    reads a
    decreases idx
{
    if idx == 0 then a[0]
    else
        var prev := MaxEnding(a, idx - 1);
        if prev + a[idx] > a[idx] then prev + a[idx] else a[idx]
}

// Maximum sum of any subarray contained entirely within a[0..limit).
function {:induction false} MaxSubarrayUpTo(a: array<int>, limit: int): int
    requires 1 <= limit <= a.Length
    reads a
    decreases limit
{
    if limit == 1 then MaxEnding(a, 0)
    else
        var prefix := MaxSubarrayUpTo(a, limit - 1);
        var ending := MaxEnding(a, limit - 1);
        if ending > prefix then ending else prefix
}

function {:induction false} MaxSubarray(a: array<int>): int
    reads a
{
    if a.Length == 0 then 0 else MaxSubarrayUpTo(a, a.Length)
}

function {:induction false} MaxElementPrefix(a: array<int>, idx: int): int
    requires 0 <= idx < a.Length
    reads a
    decreases idx
{
    if idx == 0 then a[0]
    else
        var prev := MaxElementPrefix(a, idx - 1);
        if prev > a[idx] then prev else a[idx]
}

// Maximum element in the array. When all elements are negative,
// the best subarray is a single element (the least negative one).
function {:induction false} MaxElement(a: array<int>): int
    requires a.Length > 0
    reads a
{
    MaxElementPrefix(a, a.Length - 1)
}

function {:induction false} ShiftedMaxEnding(a: array<int>, c: int, idx: int): int
    requires 0 <= idx < a.Length
    reads a
    decreases idx
{
    if idx == 0 then a[0] + c
    else
        var prev := ShiftedMaxEnding(a, c, idx - 1);
        var here := a[idx] + c;
        if prev + here > here then prev + here else here
}

function {:induction false} ShiftedMaxSubarrayUpTo(a: array<int>, c: int, limit: int): int
    requires 1 <= limit <= a.Length
    reads a
    decreases limit
{
    if limit == 1 then ShiftedMaxEnding(a, c, 0)
    else
        var prefix := ShiftedMaxSubarrayUpTo(a, c, limit - 1);
        var ending := ShiftedMaxEnding(a, c, limit - 1);
        if ending > prefix then ending else prefix
}

function {:induction false} ShiftedMaxSubarray(a: array<int>, c: int): int
    reads a
{
    if a.Length == 0 then 0 else ShiftedMaxSubarrayUpTo(a, c, a.Length)
}

// Formal specification of the maximum subarray problem.
predicate {:induction false} IsMaxSubSum(a: array<int>, value: int)
    reads a
{
    (a.Length == 0 && value == 0) ||
    (a.Length > 0 &&
        (exists s, t :: 0 <= s <= t < a.Length && value == Sum(a, s, t)) &&
        (forall s, t :: 0 <= s <= t < a.Length ==> Sum(a, s, t) <= value))
}

method {:induction false} Kadane(a: array<int>) returns (maxSum: int)
    ensures maxSum == MaxSubarray(a)
    ensures IsMaxSubSum(a, maxSum)
{
    if a.Length == 0 {
        maxSum := 0;
    } else {
        var curr := a[0];  // Max sum ending at current position
        var best := a[0];  // Global maximum seen so far
        var i := 1;
        assert curr == MaxEnding(a, 0);

        while i < a.Length
            invariant 1 <= i <= a.Length
            invariant curr == MaxEnding(a, i - 1)
            invariant best == MaxSubarrayUpTo(a, i)
            decreases a.Length - i
        {
            // Decide: extend previous subarray or start fresh here
            var nextCurr := if curr + a[i] > a[i] then curr + a[i] else a[i];
            calc {
                nextCurr;
            ==
                (if MaxEnding(a, i - 1) + a[i] > a[i] then MaxEnding(a, i - 1) + a[i] else a[i]);
            ==
                MaxEnding(a, i);
            }

            var nextBest := if nextCurr > best then nextCurr else best;
            calc {
                nextBest;
            ==
                (if MaxEnding(a, i) > MaxSubarrayUpTo(a, i) then MaxEnding(a, i) else MaxSubarrayUpTo(a, i));
            ==
                MaxSubarrayUpTo(a, i + 1);
            }

            curr := nextCurr;
            best := nextBest;
            i := i + 1;
        }
        assert i == a.Length;
        maxSum := best;
        assert maxSum == MaxSubarray(a);
    }

    MaxSubarrayIsMaximum(a);
}

// All non-negative: optimal subarray is the entire array.
// All negative: optimal subarray is the single largest (least negative) element.
// Shifted variant: proves correctness for arrays with per-element shift cost.
method {:induction false} KadaneChecks(a: array<int>, shift: int)
    ensures IsShiftedMaxSubSum(a, shift, ShiftedMaxSubarray(a, shift))
{
    var result := Kadane(a);

    if a.Length > 0 && forall k :: 0 <= k < a.Length ==> a[k] >= 0 {
        AllNonNegativeFullSum(a);
    }

    if a.Length > 0 && forall k :: 0 <= k < a.Length ==> a[k] < 0 {
        AllNegativeChoosesMax(a);
        assert result == MaxElement(a);
    }

    ShiftedMaxLemma(a, shift);
}
