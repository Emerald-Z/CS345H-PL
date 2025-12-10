// Here is a very simple AST Test Case (PL Within PL)
// Citation : Used Gemini for understanding of switch case and datatypes in Dafny

datatype Term =
  | Literal (i : int)
  | Add (lhs : Term, rhs : Term)
  | If (cond : Term, thenTerm : Term, elseTerm : Term)

datatype Result =
  | Continue (t : Term)
  | Happy (i : int)

function {:induction false} Reduce(term : Term) : Result {
  match term
  
  case Literal(val) => (Happy(val))

  case Add(lhs, rhs) => (
    match Reduce(lhs)
    case Continue(t) => Continue(Add(t, rhs))
    case Happy(lhsVal) => 
      match Reduce(rhs)
      case Continue(t) => Continue(Add(lhs, t))
      case Happy(rhsVal) => (Continue(Literal(lhsVal + rhsVal)))
  )
  
  case If(cond, thenT, elseT) => (
    match Reduce(cond)
    case Continue(t) => Continue(If(t, thenT, elseT))
    case Happy(condVal) => (
      if (condVal != 0) then
        Continue(thenT)
      else
        Continue(elseT)
    )
  )
}

function {:induction false} ReduceFully(term : Term) : int
  decreases TermSize(term)
{
  match (Reduce(term))
  case Continue(t) => (
    WellFoundedProof(term);
    ReduceFully(t)
  )
  case Happy(i) => i
}

lemma {:induction false} WellFoundedProof(term : Term)
  ensures (Reduce(term).Happy? || (Reduce(term).Continue? && (TermSize(term) > TermSize(Reduce(term).t))))
  decreases term
{
  match term
  case Literal(_) => {}
  case Add(lhs, rhs) => {
    match lhs
    case Literal(_) => {
      match rhs
      case Literal(_) => {}
      case _ => WellFoundedProof(rhs);
    }
    case _ => WellFoundedProof(lhs);
  }
  case If(cond, thenT, elseT) =>
    match cond
    case Literal(condVal) => {}
    case _ => WellFoundedProof(cond);
}

function {:induction false} TermSize(term : Term) : int 
  ensures TermSize(term) >= 1
{
  match term
  case Literal(_) => 1
  case Add(lhs, rhs) => TermSize(lhs) + TermSize(rhs) + 1
  case If(cond, thenTerm, elseTerm) => TermSize(cond) + TermSize(thenTerm) + TermSize(elseTerm) + 1
}

function {:induction false} LargeStepReduction(term : Term) : int
{
  match term
  
  case Literal(val) => val

  case Add(lhs, rhs) => LargeStepReduction(lhs) + LargeStepReduction(rhs)
  
  case If(cond, thenT, elseT) => (
    if (LargeStepReduction(cond) != 0) then
        LargeStepReduction(thenT)
      else
        LargeStepReduction(elseT)
  )
}

method {:induction false} WellFoundedTest(term : Term) {
  assert (ReduceFully(term) == LargeStepReduction(term)) by {
    SmallAndLargeReductionEqualProof(term);
  }
}
