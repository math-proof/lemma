module
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Int.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Ring
public import Theorem.Combinatorics.Enumerative.FaultFree3xnTiling.Part14


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FaultFree3xnTiling.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
namespace MetaMathlibExt

noncomputable def ff3CodeEdgeEquiv (n : ℕ) :
    ff3Code ∅ n ≃ ff3FaultFreeEdgeMatchings n where
  toFun c := ⟨ff3CodeEdges c, ff3_codeEdges_isMatching c, ff3_codeEdges_crosses c⟩
  invFun E := ff3EdgeCode E
  left_inv := ff3_edgeCode_codeEdges
  right_inv E := Subtype.ext (ff3_codeEdges_edgeCode E)

end MetaMathlibExt
