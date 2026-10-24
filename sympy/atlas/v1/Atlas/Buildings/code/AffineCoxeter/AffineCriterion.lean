/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/AffineCriterion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.AffineCoxeter.PerronFrobeniusProof
import sympy.atlas.v1.Atlas.Buildings.code.AffineCoxeter.TitsConeConvexity
import sympy.atlas.v1.Atlas.Buildings.code.AffineCoxeter.TitsConeFiniteParabolic

set_option maxHeartbeats 800000

set_option linter.unusedSectionVars false

open Finset BigOperators CoxeterGroup TitsCone

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- A Coxeter matrix is of **affine type** if its bilinear form is indecomposable, positive
semidefinite, and degenerate. Equivalently, it has Coxeter graph of affine Dynkin type. -/
def IsAffineCoxeter (M : CoxeterMatrix B) : Prop :=
  FormIndecomposable (fun s t => formVal M s t) ∧
  (∀ v : B → ℝ, bilinForm M v v ≥ 0) ∧
  (∃ v : B → ℝ, v ≠ 0 ∧ bilinForm M v v = 0)

/-- The **affine hyperplane** $E = \{\mu : \langle v_0, \mu\rangle = 1\}$ on which the affine Weyl
group acts. Here $v_0$ is the positive radical vector of the Coxeter form. -/
def affineHyperplane (_M : CoxeterMatrix B) (v₀ : B → ℝ) : Set (B → ℝ) :=
  {μ | ∑ s, v₀ s * μ s = 1}

/-- Typeclass packaging the **convexity** of the Tits cone $\mathcal U$. Used locally to allow
the affine criterion to be stated abstractly. -/
class TitsConeConvexity {B : Type*} [DecidableEq B] [Fintype B]
    (M : CoxeterMatrix B) : Prop where
  convex : ∀ (x y : B → ℝ), x ∈ titsConeSet M → y ∈ titsConeSet M →
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    (fun s => (1 - t) * x s + t * y s) ∈ titsConeSet M

/-- Default instance: convexity of $\mathcal U$ follows from `titsConeSet_convex`. -/
instance titsConeConvexity_instance (M : CoxeterMatrix B) : TitsConeConvexity M where
  convex := by
    intro x y hx hy t ht0 ht1
    have h1t : 0 ≤ 1 - t := by linarith
    have hab : (1 - t) + t = 1 := by ring
    have hconv := titsConeSet_convex M hx hy h1t ht0 hab
    convert hconv using 1

/-- Typeclass packaging the **chamber-chasing / orbit-density** property: every point of the
affine hyperplane $E$ lies on a segment between two points of the Tits cone. -/
class ChamberChasingProperty {B : Type*} [DecidableEq B] [Fintype B]
    (M : CoxeterMatrix B) : Prop where
  orbit_density :
    ∀ (v₀ : B → ℝ),
    (∀ s, v₀ s > 0) →
    (∀ t : B, ∑ u : B, v₀ u * formVal M u t = 0) →
    IsAffineCoxeter M →
    ∀ (x : B → ℝ), x ∈ affineHyperplane M v₀ →
    ∃ (p₁ p₂ : B → ℝ) (t : ℝ),
      p₁ ∈ titsConeSet M ∧ p₂ ∈ titsConeSet M ∧
      0 ≤ t ∧ t ≤ 1 ∧
      (∀ s, x s = (1 - t) * p₁ s + t * p₂ s)

/-- Default constructor: chamber-chasing follows from the local finiteness of nonposRoots and the
characterization of the Tits cone in terms of $\nu$-finite points. -/
theorem chamberChasingProperty_instance
    {B : Type*} [DecidableEq B] [Fintype B]
    (M : CoxeterMatrix B) [RootSystemData M] :
    ChamberChasingProperty M := by
  constructor
  intro v₀ hv₀_pos hv₀_rad _hAff x hx

  have hx_ne : x ≠ 0 := by
    intro hx_eq
    subst hx_eq
    simp only [affineHyperplane, Set.mem_setOf_eq, Pi.zero_apply, mul_zero,
      Finset.sum_const_zero] at hx
    norm_num at hx


  have hx_sum : ∑ s, v₀ s * x s = 1 := by
    simp only [affineHyperplane, Set.mem_setOf_eq] at hx; exact hx
  have hnu : nuFiniteAt (RootSystemData.Φpos (M := M)) x :=
    RootSystemData.nonposRoots_finite_on_hyperplane v₀ hv₀_pos hv₀_rad x hx_sum

  have hx_cone := nuFinite_mem_titsCone M x hx_ne hnu

  exact ⟨x, x, 0, hx_cone, hx_cone, le_refl 0, zero_le_one, fun s => by ring⟩

/-- Instance form of `chamberChasingProperty_instance`. -/
noncomputable instance (M : CoxeterMatrix B) [RootSystemData M] :
    ChamberChasingProperty M := chamberChasingProperty_instance M
