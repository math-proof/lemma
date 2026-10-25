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
import Abbrev.Combinatorics.Enumerative.FaultFree3xnTiling.Part7


namespace MetaMathlibExt

noncomputable def ff3CodeEdges {n : ℕ} (c : ff3Code ∅ n) :
    Finset (ff3Edge n) := by
  classical
  exact Finset.univ.filter fun e ↦ match e with
      | Sum.inl e => e.1 ∈ ff3ProfileRows (c.1 e.2)
      | Sum.inr e => (c.2 e.2).1 = some e.1

end MetaMathlibExt
