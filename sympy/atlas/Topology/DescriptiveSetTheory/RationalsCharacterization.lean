/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/RationalsCharacterization.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.Topology.Perfect
import Mathlib.Topology.Instances.Rat
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.PerfectSpace
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Tactic.Linarith
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.UniformSpace.Uniformizable

section

/-!
# Sierpinski's characterization of the rationals
-/

noncomputable section

open Set Filter

namespace MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

/-- A block pairs corresponding clopen sets with optional matched points. -/
private structure Block (X Y : Type*) where
  UX : Set X
  UY : Set Y
  pt : Option (X × Y)
  bound : ℕ

/-- Good states are finite covering partitions into matched/unmatched blocks. -/
private def IsGood {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [PseudoMetricSpace X] [PseudoMetricSpace Y] (l : List (Block X Y)) : Prop :=
  (∀ b ∈ l, IsClopen b.UX ∧ IsClopen b.UY ∧ b.UX.Nonempty ∧ b.UY.Nonempty) ∧
  (∀ b ∈ l, ∀ s t, b.pt = some (s, t) → s ∈ b.UX ∧ t ∈ b.UY) ∧
  (∀ b1 ∈ l, ∀ b2 ∈ l, b1 ≠ b2 → Disjoint b1.UX b2.UX ∧ Disjoint b1.UY b2.UY) ∧
  l.Nodup ∧
  ((∀ x, ∃ b ∈ l, x ∈ b.UX) ∧ (∀ y, ∃ b ∈ l, y ∈ b.UY)) ∧
  (∀ b ∈ l, ∀ s t n, b.pt = some (s, t) → b.bound = n →
    b.UX ⊆ Metric.ball s (1 / ((n + 1 : ℕ) : ℝ)) ∧
    b.UY ⊆ Metric.ball t (1 / ((n + 1 : ℕ) : ℝ)))

/-- Good states as sets: finite covering partitions into blocks. -/
private def IsGoodS {X Y : Type*}
    [PseudoMetricSpace X] [PseudoMetricSpace Y] (s : Set (Block X Y)) : Prop :=
  s.Finite ∧
  (∀ b ∈ s, IsClopen b.UX ∧ IsClopen b.UY ∧ b.UX.Nonempty ∧ b.UY.Nonempty) ∧
  (∀ b ∈ s, ∀ p q, b.pt = some (p, q) → p ∈ b.UX ∧ q ∈ b.UY) ∧
  (∀ b1 ∈ s, ∀ b2 ∈ s, b1 ≠ b2 → Disjoint b1.UX b2.UX ∧ Disjoint b1.UY b2.UY) ∧
  ((∀ x, ∃ b ∈ s, x ∈ b.UX) ∧ (∀ y, ∃ b ∈ s, y ∈ b.UY)) ∧
  (∀ b ∈ s, ∀ p q n, b.pt = some (p, q) → b.bound = n →
    b.UX ⊆ Metric.ball p (1 / ((n + 1 : ℕ) : ℝ)) ∧
    b.UY ⊆ Metric.ball q (1 / ((n + 1 : ℕ) : ℝ)))

/-- Swap X and Y sides of a block. -/
private def Block.swap {X Y : Type*} (b : Block X Y) : Block Y X :=
  ⟨b.UY, b.UX, b.pt.map Prod.swap, b.bound⟩
end MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted
end
