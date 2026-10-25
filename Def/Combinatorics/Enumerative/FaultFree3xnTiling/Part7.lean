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
import Theorem.Combinatorics.Enumerative.FaultFree3xnTiling.Part5


namespace MetaMathlibExt

def ff3IsEdgeMatching {n : ℕ} (E : Finset (ff3Edge n)) : Prop :=
  ∀ e ∈ E, ∀ f ∈ E, e ≠ f → Disjoint (ff3EdgeDomino e) (ff3EdgeDomino f)

def ff3CrossesEveryCut {n : ℕ} (E : Finset (ff3Edge n)) : Prop :=
  ∀ k : Fin n, ∃ r : Fin 3, Sum.inl (r, k) ∈ E

end MetaMathlibExt
