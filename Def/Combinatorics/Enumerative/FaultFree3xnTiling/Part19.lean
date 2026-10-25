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
import Theorem.Combinatorics.Enumerative.FaultFree3xnTiling.Part14


namespace MetaMathlibExt

noncomputable def ff3CodeEdgeEquiv (n : ℕ) :
    ff3Code ∅ n ≃ ff3FaultFreeEdgeMatchings n where
  toFun c := ⟨ff3CodeEdges c, ff3_codeEdges_isMatching c, ff3_codeEdges_crosses c⟩
  invFun E := ff3EdgeCode E
  left_inv := ff3_edgeCode_codeEdges
  right_inv E := Subtype.ext (ff3_codeEdges_edgeCode E)

end MetaMathlibExt
