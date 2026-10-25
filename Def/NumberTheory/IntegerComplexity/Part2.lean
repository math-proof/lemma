/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/IntegerComplexity.lean -/

import Mathlib.Data.PNat.Basic
import Mathlib.Data.Nat.Find
import Theorem.NumberTheory.IntegerComplexity


namespace IntegerComplexity

/-- Predicate: leaf count `c` is achievable for `n`. Replaces Set S. -/
def Pred (n : ℕ+) (c : ℕ) : Prop := ∃ e : Expr, e.eval = (n : ℕ) ∧ e.count = c

end IntegerComplexity
