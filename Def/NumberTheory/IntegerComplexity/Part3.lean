/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/IntegerComplexity.lean -/

import Mathlib.Data.PNat.Basic
import Mathlib.Data.Nat.Find
import Theorem.NumberTheory.IntegerComplexity.Part2


namespace IntegerComplexity

/-- Integer complexity: least number of ones needed to express `n`
    using `1`, `+`, `*` and parentheses. Source C4.
    Implemented via Nat.find on proved existential predicate. -/
noncomputable def complexity (n : ℕ+) : ℕ := by
  classical
  exact Nat.find (Pred_nonempty n)

end IntegerComplexity
