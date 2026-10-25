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
import Theorem.Combinatorics.Enumerative.FaultFree3xnTiling.Part10


namespace MetaMathlibExt

def ff3EdgeProfileRows {n : ℕ} (E : ff3FaultFreeEdgeMatchings n) (k : Fin n) :
    Finset (Fin 3) :=
  Finset.univ.filter fun r ↦ Sum.inl (r, k) ∈ E.1

end MetaMathlibExt
