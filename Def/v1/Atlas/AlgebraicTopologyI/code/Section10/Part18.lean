/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section5
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section11
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.LocalityPrinciple
import Def.v1.Atlas.AlgebraicTopologyI.code.Section5.Part6
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section11
import Def.v1.Atlas.AlgebraicTopologyI.code.LocalityPrinciple.Part5
import Abbrev.v1.Atlas.AlgebraicTopologyI.code.Section10.Part5
open CategoryTheory CategoryTheory.Limits AlgebraicTopologyI


namespace BrouwerFixedPoint

open Metric Set Inner

/-- The inclusion `S^{n-1} ↪ D^n` of the boundary sphere into the disk, as a morphism of
`TopCat`. -/
noncomputable def sphereInclusion (n : ℕ) :
    TopCat.of ↥(Sphere n) ⟶ TopCat.of ↥(Disk n) :=
  TopCat.ofHom ⟨Set.inclusion Metric.sphere_subset_closedBall,
    continuous_inclusion _⟩


/-- A retraction `r : ℝ^n → ℝ^n` of `D^n` onto `S^{n-1}` packaged as a `TopCat` morphism
`D^n ⟶ S^{n-1}`. -/
noncomputable def diskRetraction (n : ℕ)
    (r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hr : IsRetraction n r) :
    TopCat.of ↥(Disk n) ⟶ TopCat.of ↥(Sphere n) :=
  TopCat.ofHom ⟨fun ⟨x, hx⟩ => ⟨r x, hr.maps_to x hx⟩,
    Continuous.subtype_mk (hr.continuous_r.comp continuous_subtype_val) _⟩


/-- The projection `ℝ^1 → ℝ` onto the (only) coordinate, as a continuous linear map. -/
noncomputable def coordProj : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ :=
  EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)


/-- **No retraction `D^{m+1} → S^m`** for `m ≥ 1` (inductive step for Brouwer). If such a
retraction existed, then `H_m(S^m) ≅ ℤ` would be a retract of `H_m(D^{m+1}) = 0`,
contradiction. -/
noncomputable def rayDiscrim {n : ℕ} (a v : EuclideanSpace ℝ (Fin n)) : ℝ :=
  inner (𝕜 := ℝ) a v ^ 2 + ‖v‖ ^ 2 * (1 - ‖a‖ ^ 2)

/-- The positive root `t = (−⟨a,v⟩ + √Δ) / ‖v‖²` of the equation `‖a + t v‖ = 1`, where
`Δ = rayDiscrim a v`. Geometrically: the parameter at which the ray `t ↦ a + t v`
(with `t ≥ 0`) hits the unit sphere. -/
noncomputable def rayParam {n : ℕ} (a v : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (-inner (𝕜 := ℝ) a v + Real.sqrt (rayDiscrim a v)) / ‖v‖ ^ 2

/-- Geometric retraction associated to a fixed-point-free self-map `f` of `D^n`: from each
point `x`, follow the ray from `f x` through `x` until it hits the boundary sphere. -/
noncomputable def retractionMap {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  f x + rayParam (f x) (x - f x) • (x - f x)

/-- Radial projection of `ℝ^n` onto the closed unit ball: `x ↦ x / max(1, ‖x‖)`. -/
noncomputable def projBall {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  (max 1 ‖x‖)⁻¹ • x

/-- A subset `A ⊆ B` is a *deformation retract within `B`* if `A ⊆ B` and there exists a
deformation retraction of `B` onto `A` (viewed as a subset of `B`). Hypothesis of
Corollary 10.3. -/
def IsSubspaceDeformationRetract {X : Type u} [TopologicalSpace X] (A B : Set X) : Prop :=
  A ⊆ B ∧ Nonempty (DeformationRetract.IsDeformationRetract (Subtype.val ⁻¹' A : Set ↥B))

/-- The equivalence relation on `X` that collapses the subset `A` to a single point: two points
are related iff they are equal, or both lie in `A`. Used to form the quotient `X / A`. -/
def collapseSetoid {X : Type u} [TopologicalSpace X] (A : Set X) : Setoid X where
  r x y := x = y ∨ (x ∈ A ∧ y ∈ A)
  iseqv := {
    refl := fun _ => Or.inl rfl
    symm := fun h => h.elim (fun heq => Or.inl heq.symm) (fun ⟨hx, hy⟩ => Or.inr ⟨hy, hx⟩)
    trans := fun h1 h2 => by
      rcases h1 with rfl | ⟨hx, _⟩
      · exact h2
      · rcases h2 with rfl | ⟨_, hz⟩ <;> exact Or.inr ⟨hx, ‹_›⟩
  }

/-- The quotient space `X / A`: the set of equivalence classes of `collapseSetoid A`, with the
quotient topology. -/
def QuotientSpace (X : Type u) [TopologicalSpace X] (A : Set X) :=
  Quotient (collapseSetoid A)

end BrouwerFixedPoint
