module
public import Def.v1.Atlas.LieGroups.code.Admissible.Part3
public import Mathlib.Algebra.Lie.OfAssociative
public import Def.v1.Atlas.LieGroups.code.ContinuousRep.Part3
public import Theorem.LinearMap.EqContinuousLinearEquivOfBijective.of.Bijective
public import Theorem.Real.GetToMonoidHom.in.SmoothSubspace.of.In_SmoothSubspace
public import Def.v1.Atlas.LieGroups.code.GKModule.Part2
public import Def.v1.Atlas.LieGroups.code.GKModuleDefs.Part2
public import Def.v1.Atlas.LieGroups.code.SmoothVectors
public import Def.v1.Atlas.LieGroups.code.KFiniteProps.Part4
public import Theorem.v1.Atlas.LieGroups.code.HarishChandraFunctor.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HarishChandraFunctor.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

set_option autoImplicit false

attribute [local instance 100] LieRing.ofAssociativeRing

set_option maxHeartbeats 800000

open scoped Manifold

open ContinuousRep

def repHom_restrict_kFinite
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℂ F₁]
    {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℂ F₂]
    (π₁ : ContinuousRep G F₁) (π₂ : ContinuousRep G F₂)
    (K_sub : Subgroup G)
    (T : RepHom π₁ π₂) :
    ↥(π₁.kFiniteSubspace K_sub) →ₗ[ℂ] ↥(π₂.kFiniteSubspace K_sub) where
  toFun v := ⟨T.toContinuousLinearMap v.val,
    repHom_maps_kFinite π₁ π₂ K_sub T v.val v.prop⟩
  map_add' u v := by
    apply Subtype.ext
    simp
  map_smul' c v := by
    apply Subtype.ext
    simp

end
