module
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Int.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Ring
public import Abbrev.Combinatorics.Enumerative.FaultFree3xnTiling.Part7


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FaultFree3xnTiling.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
namespace MetaMathlibExt

noncomputable def ff3CodeEdges {n : ℕ} (c : ff3Code ∅ n) :
    Finset (ff3Edge n) := by
  classical
  exact Finset.univ.filter fun e ↦ match e with
      | Sum.inl e => e.1 ∈ ff3ProfileRows (c.1 e.2)
      | Sum.inr e => (c.2 e.2).1 = some e.1

end MetaMathlibExt
