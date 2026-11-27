/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/IntegerComplexity.lean -/

module

public import Mathlib.Data.PNat.Basic
public import Mathlib.Data.Nat.Find
public import Theorem.NumberTheory.IntegerComplexity
public import Notation.Data.PNat

@[expose] public section

namespace IntegerComplexity

/-- Predicate: leaf count `c` is achievable for `n`. Replaces Set S. -/
def Pred (n : ℕ⁺) (c : ℕ) : Prop := ∃ e : Expr, e.eval = (n : ℕ) ∧ e.count = c

end IntegerComplexity
