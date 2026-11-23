/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NewtonSequenceTest.lean -/
module

public import Def.NumberTheory.NewtonSequence
public import Theorem.Nat.NewtonSequence

public section

namespace MetaMathlibExt

example {R : Type*} [CommSemiring R] (a c : ℕ → R) (h : IsNewtonSequence a c) :
    a 1 = c 1 := by
  simpa using h.eq_recurrence 0

example {R : Type*} [CommSemiring R] (a c : ℕ → R) (h : IsNewtonSequence a c) :
    a 2 = a 1 * c 1 + 2 * c 2 := by
  simpa [Finset.range_one] using h.eq_recurrence 1

end MetaMathlibExt
