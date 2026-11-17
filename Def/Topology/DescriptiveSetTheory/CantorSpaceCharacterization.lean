/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/CantorSpaceCharacterization.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

module

public import Mathlib.Topology.Perfect
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Separation.Profinite

@[expose] public section

/-!
# Brouwer's characterization of Cantor space
-/


section

noncomputable section

namespace MathlibExt.Topology.DescriptiveSetTheory.CantorSpaceCharacterizationWanted

def brouwerStep {X : Type*} (kids : ℕ → Set X → List (Set X)) :
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

def brouwerState {X : Type*} (kids : ℕ → Set X → List (Set X)) (t : List Bool) :
    List (Set X) × ℕ :=
  t.foldl (brouwerStep kids) ([Set.univ], 0)

def brouwerPiece {X : Type*} (kids : ℕ → Set X → List (Set X)) (t : List Bool) :
    Set X :=
  ⋃ s ∈ (brouwerState kids t).1, s

def brouwerPref (σ : ℕ → Bool) (n : ℕ) : List Bool :=
  (List.range n).map σ

end MathlibExt.Topology.DescriptiveSetTheory.CantorSpaceCharacterizationWanted
end
end
