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
public import Def.v1.Atlas.LieGroups.code.HarishChandraFunctor


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

theorem kFiniteSubspace_kAction_locallyFinite
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G) :
    (kFiniteSubspace_kAction π K_sub).IsLocallyFinite := by
  sorry

end
