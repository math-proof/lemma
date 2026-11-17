/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/RiordanAZSequences.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Data.Finset.Range
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Substitution

@[expose] public section

namespace MetaMathlibExt

noncomputable def raz_triangularCoeff (a : ℕ → ℚ) (b : ℕ → ℕ → ℚ)
    (n : ℕ) : ℚ :=
  Nat.strongRec (motive := fun _ ↦ ℚ) (fun n ih ↦
    (a n - ∑ j ∈ Finset.range n, (if h : j < n then ih j h else 0) * b n j) / b n n) n

end MetaMathlibExt
