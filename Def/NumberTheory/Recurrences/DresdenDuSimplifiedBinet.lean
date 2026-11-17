/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/DresdenDuSimplifiedBinet.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

section

namespace MetaMathlibExt

/-- Positive left-eigenvector weights for the `k`-step recurrence. -/
noncomputable def ddb_weight (k : ℕ) (α : ℝ) (i : ℕ) : ℝ :=
  1 - α ^ ((i : ℤ) - (k : ℤ))

end MetaMathlibExt
end
