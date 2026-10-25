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
import Def.Combinatorics.Enumerative.FaultFree3xnTiling.Part15


namespace MetaMathlibExt

theorem ff3_edgeProfileRows_nonempty {n : ℕ} (E : ff3FaultFreeEdgeMatchings n)
    (k : Fin n) : (ff3EdgeProfileRows E k).Nonempty := by
  obtain ⟨r, hr⟩ := E.property.2 k
  exact ⟨r, by simp [ff3EdgeProfileRows, hr]⟩

end MetaMathlibExt
