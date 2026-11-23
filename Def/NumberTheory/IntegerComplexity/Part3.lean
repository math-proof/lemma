/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/IntegerComplexity.lean -/

module

public import Mathlib.Data.PNat.Basic
public import Mathlib.Data.Nat.Find
public import Theorem.NumberTheory.IntegerComplexity.Part2

@[expose] public section

namespace IntegerComplexity

/-- Integer complexity: least number of ones needed to express `n`
    using `1`, `+`, `*` and parentheses. Source C4.
    Implemented via Nat.find on proved existential predicate. -/
noncomputable def complexity (n : ℕ+) : ℕ := by
  classical
  exact Nat.find (Pred_nonempty n)

end IntegerComplexity
