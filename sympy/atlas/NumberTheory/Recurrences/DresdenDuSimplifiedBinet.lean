/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/DresdenDuSimplifiedBinet.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section

namespace MetaMathlibExt

/-- Positive left-eigenvector weights for the `k`-step recurrence. -/
private noncomputable def ddb_weight (k : ℕ) (α : ℝ) (i : ℕ) : ℝ :=
  1 - α ^ ((i : ℤ) - (k : ℤ))
end MetaMathlibExt
end
