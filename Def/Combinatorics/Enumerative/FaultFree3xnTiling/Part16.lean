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
import Theorem.Combinatorics.Enumerative.FaultFree3xnTiling.Part11


namespace MetaMathlibExt

noncomputable def ff3EdgeProfile {n : ℕ} (E : ff3FaultFreeEdgeMatchings n)
    (k : Fin n) : ff3Profile :=
  ff3ProfileEquiv.symm ⟨ff3EdgeProfileRows E k, ff3_edgeProfileRows_nonempty E k⟩

end MetaMathlibExt
