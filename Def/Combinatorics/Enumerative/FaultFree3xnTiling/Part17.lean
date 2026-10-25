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
import Theorem.Combinatorics.Enumerative.FaultFree3xnTiling.Part12


namespace MetaMathlibExt

noncomputable def ff3EdgeVertical {n : ℕ} (E : ff3FaultFreeEdgeMatchings n)
    (j : Fin (n + 1)) : Option (Fin 2) :=
  if Sum.inr ((0 : Fin 2), j) ∈ E.1 then some 0
  else if Sum.inr ((1 : Fin 2), j) ∈ E.1 then some 1 else none

end MetaMathlibExt
