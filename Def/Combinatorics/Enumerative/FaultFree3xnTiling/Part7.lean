module
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Int.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Ring
public import Theorem.Combinatorics.Enumerative.FaultFree3xnTiling.Part5


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FaultFree3xnTiling.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
namespace MetaMathlibExt

def ff3IsEdgeMatching {n : ℕ} (E : Finset (ff3Edge n)) : Prop :=
  ∀ e ∈ E, ∀ f ∈ E, e ≠ f → Disjoint (ff3EdgeDomino e) (ff3EdgeDomino f)

def ff3CrossesEveryCut {n : ℕ} (E : Finset (ff3Edge n)) : Prop :=
  ∀ k : Fin n, ∃ r : Fin 3, Sum.inl (r, k) ∈ E

end MetaMathlibExt
