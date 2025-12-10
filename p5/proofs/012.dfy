lemma {:induction false} SmallAndLargeReductionEqualProof(term : Term)
    ensures ReduceFully(term) == LargeStepReduction(term)
{
    match term {
        case Literal(val) => {
            // Base case: Literal(val) -> val
        }
        case Add(lhs, rhs) => {
            // ReduceFully(Add(lhs, rhs)) = LargeStepReduction(lhs) + LargeStepReduction(rhs)
            SmallAndLargeReductionEqualProof(lhs);
            SmallAndLargeReductionEqualProof(rhs);
            
            ReduceFullyAddLemma(lhs, rhs);
            assert ReduceFully(term) == LargeStepReduction(lhs) + LargeStepReduction(rhs);
        }
        case If(cond, thenT, elseT) => {
            SmallAndLargeReductionEqualProof(cond);
            SmallAndLargeReductionEqualProof(thenT);
            SmallAndLargeReductionEqualProof(elseT);
            
            // ReduceFully(If(cond, thenT, elseT)) equals the appropriate branch
            ReduceFullyIfLemma(cond, thenT, elseT);
        }
    }
}

lemma {:induction false} ReduceFullyAddLemma(lhs : Term, rhs : Term)
    ensures ReduceFully(Add(lhs, rhs)) == ReduceFully(lhs) + ReduceFully(rhs)
    decreases TermSize(Add(lhs, rhs))
{
    match Reduce(lhs) {
        case Happy(lhsVal) => {
            match Reduce(rhs) {
                case Happy(rhsVal) => {
                    // Both sides are fully reduced
                    assert ReduceFully(lhs) == lhsVal;
                    assert ReduceFully(rhs) == rhsVal;
                }
                case Continue(rhs') => {
                    // rhs needs more reduction
                    WellFoundedProof(rhs);
                    assert TermSize(rhs') < TermSize(rhs);
                    assert TermSize(Add(lhs, rhs')) < TermSize(Add(lhs, rhs));
                    assert ReduceFully(rhs) == ReduceFully(rhs');
                    ReduceFullyAddLemma(lhs, rhs');
                    assert ReduceFully(Add(lhs, rhs')) == ReduceFully(lhs) + ReduceFully(rhs');
                }
            }
        }
        case Continue(lhs') => {
            WellFoundedProof(lhs);
            ReduceFullyAddLemma(lhs', rhs);
            assert ReduceFully(Add(lhs', rhs)) == ReduceFully(lhs') + ReduceFully(rhs);
            assert ReduceFully(Add(lhs, rhs)) == ReduceFully(Add(lhs', rhs));
        }
    }
}

lemma {:induction false} ReduceFullyIfLemma(cond : Term, thenT : Term, elseT : Term)
    ensures ReduceFully(If(cond, thenT, elseT)) == 
        (if ReduceFully(cond) != 0 then ReduceFully(thenT) else ReduceFully(elseT))
    decreases TermSize(If(cond, thenT, elseT))
{
    match Reduce(cond) {
        case Happy(condVal) => {
            // cond is fully reduced
        }
        case Continue(cond') => {
            WellFoundedProof(cond);
            assert TermSize(If(cond', thenT, elseT)) < TermSize(If(cond, thenT, elseT));
            ReduceFullyIfLemma(cond', thenT, elseT);
        }
    }
}