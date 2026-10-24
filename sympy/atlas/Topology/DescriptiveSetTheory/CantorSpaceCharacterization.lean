/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/CantorSpaceCharacterization.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.Topology.Perfect
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Separation.Profinite

section
/-!
# Brouwer's characterization of Cantor space
-/

noncomputable section

namespace MathlibExt.Topology.DescriptiveSetTheory.CantorSpaceCharacterizationWanted

private def brouwerStep {X : Type*} (kids : ℕ → Set X → List (Set X)) :
    List (Set X) × ℕ → Bool → List (Set X) × ℕ
  | ([], n), _ => ([], n)
  | ([C], n), false =>
    match kids n C with
    | [] => ([C], n + 1)
    | [a] => ([a], n + 1)
    | a :: _rest => ([a], n + 1)
  | ([C], n), true =>
    match kids n C with
    | [] => ([C], n + 1)
    | [a] => ([a], n + 1)
    | _a :: rest => (rest, n + 1)
  | (C :: _D :: _rest, n), false => ([C], n)
  | (_C :: D :: rest, n), true => ((D :: rest), n)

private def brouwerState {X : Type*} (kids : ℕ → Set X → List (Set X)) (t : List Bool) :
    List (Set X) × ℕ :=
  t.foldl (brouwerStep kids) ([Set.univ], 0)

private def brouwerPiece {X : Type*} (kids : ℕ → Set X → List (Set X)) (t : List Bool) :
    Set X :=
  ⋃ s ∈ (brouwerState kids t).1, s

private def brouwerPref (σ : ℕ → Bool) (n : ℕ) : List Bool :=
  (List.range n).map σ
end MathlibExt.Topology.DescriptiveSetTheory.CantorSpaceCharacterizationWanted
