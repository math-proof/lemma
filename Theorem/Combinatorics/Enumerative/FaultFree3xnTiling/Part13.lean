/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FaultFree3xnTiling.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.FaultFree3xnTiling.Part17


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
