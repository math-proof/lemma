/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HarishChandraFunctor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.Admissible.Part3
import Mathlib.Algebra.Lie.OfAssociative
import Def.v1.Atlas.LieGroups.code.ContinuousRep.Part3
import Lemma.Bijective.EqContinuousLinearEquivOfBijective.of.Bijective
import Lemma.Real.GetToMonoidHom.in.SmoothSubspace.of.In_SmoothSubspace
import Def.v1.Atlas.LieGroups.code.GKModule.Part2
import Def.v1.Atlas.LieGroups.code.GKModuleDefs.Part2
import Def.v1.Atlas.LieGroups.code.SmoothVectors
import Def.v1.Atlas.LieGroups.code.KFiniteProps.Part4
import Def.v1.Atlas.LieGroups.code.HarishChandraFunctor.Part2


noncomputable section

set_option autoImplicit false

attribute [local instance 100] LieRing.ofAssociativeRing

set_option maxHeartbeats 800000

open scoped Manifold

open ContinuousRep

theorem repHom_maps_kFinite
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℂ F₁]
    {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℂ F₂]
    (π₁ : ContinuousRep G F₁) (π₂ : ContinuousRep G F₂)
    (K_sub : Subgroup G)
    (T : RepHom π₁ π₂)
    (v : F₁) (hv : v ∈ π₁.kFiniteSubspace K_sub) :
    T.toContinuousLinearMap v ∈ π₂.kFiniteSubspace K_sub := by
  sorry

end
