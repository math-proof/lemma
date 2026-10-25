/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/RiordanAZSequences.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Rat
import Mathlib.Data.Finset.Range
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Substitution


namespace MetaMathlibExt

noncomputable def raz_triangularCoeff (a : ℕ → ℚ) (b : ℕ → ℕ → ℚ)
    (n : ℕ) : ℚ :=
  Nat.strongRec (motive := fun _ ↦ ℚ) (fun n ih ↦
    (a n - ∑ j ∈ Finset.range n, (if h : j < n then ih j h else 0) * b n j) / b n n) n

end MetaMathlibExt
