module
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Int.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Ring
public import Def.Combinatorics.Enumerative.FaultFree3xnTiling.Part17


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FaultFree3xnTiling.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
namespace MetaMathlibExt

theorem ff3_edgeVertical_eq_some_iff {n : ℕ} (E : ff3FaultFreeEdgeMatchings n)
    (r : Fin 2) (j : Fin (n + 1)) :
    ff3EdgeVertical E j = some r ↔ Sum.inr (r, j) ∈ E.1 := by
  fin_cases r
  · simp [ff3EdgeVertical]
  · by_cases h0 : Sum.inr ((0 : Fin 2), j) ∈ E.1
    · have h1 : Sum.inr ((1 : Fin 2), j) ∉ E.1 := by
        intro h
        exact ff3_edge_no_both_vertical E j ⟨h0, h⟩
      simp [ff3EdgeVertical, h0, h1]
    · simp [ff3EdgeVertical, h0]

end MetaMathlibExt
