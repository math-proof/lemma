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
import Theorem.Combinatorics.Enumerative.FaultFree3xnTiling


namespace MetaMathlibExt

/-- A square-and-domino tiling is a disjoint family of valid tiles covering
every cell of the rectangle. -/
def IsSquareDominoTiling {n : ℕ} (T : Finset (Finset (TilingCell n))) : Prop :=
  (∀ d ∈ T, IsSquareOrDomino d) ∧
    (∀ d₁ ∈ T, ∀ d₂ ∈ T, d₁ ≠ d₂ → Disjoint d₁ d₂) ∧
      ∀ x : TilingCell n, ∃ d ∈ T, x ∈ d

/-- A tiling is vertical-fault-free when every internal vertical boundary is
crossed by a horizontal domino. -/
def IsVerticalFaultFree {n : ℕ} (T : Finset (Finset (TilingCell n))) : Prop :=
  ∀ k : ℕ, k + 1 < n →
    ∃ d ∈ T, ∃ x ∈ d, ∃ y ∈ d,
      x.1 = y.1 ∧ x.2.val = k ∧ y.2.val = k + 1

def ff3IsDomino {n : ℕ} (d : Finset (TilingCell n)) : Prop :=
  d.card = 2 ∧
    ∀ x ∈ d, ∀ y ∈ d, x ≠ y → TilingCell.Adjacent x y

def ff3IsMatching {n : ℕ} (D : Finset (Finset (TilingCell n))) : Prop :=
  (∀ d ∈ D, ff3IsDomino d) ∧
    ∀ d₁ ∈ D, ∀ d₂ ∈ D, d₁ ≠ d₂ → Disjoint d₁ d₂

end MetaMathlibExt
