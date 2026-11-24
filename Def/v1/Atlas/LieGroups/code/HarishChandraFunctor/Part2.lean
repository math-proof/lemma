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
public import Theorem.v1.Atlas.LieGroups.code.HarishChandraFunctor


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

def harishChandraGKModule
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    (_hadm : π.IsAdmissible K_sub)
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (𝔨 : LieSubalgebra ℂ 𝔤)
    (Ad : K_sub →* (𝔤 →ₗ[ℂ] 𝔤))
    (_ι : 𝔤 →ₗ⁅ℂ⁆ (F →ₗ[ℂ] F))
    [LieRingModule 𝔤 ↥(π.kFiniteSubspace K_sub)]
    [LieModule ℂ 𝔤 ↥(π.kFiniteSubspace K_sub)]
    (hequiv : ∀ (k : K_sub) (X : 𝔤) (v : ↥(π.kFiniteSubspace K_sub)),
      (kFiniteSubspace_kAction π K_sub) k (⁅X, v⁆) =
        ⁅Ad k X, (kFiniteSubspace_kAction π K_sub) k v⁆) :
    GKModule 𝔤 K_sub 𝔨 Ad ↥(π.kFiniteSubspace K_sub) where
  σ := kFiniteSubspace_kAction π K_sub
  locallyFinite := kFiniteSubspace_kAction_locallyFinite π K_sub
  diffσ := (LieModule.toEnd ℂ 𝔤 ↥(π.kFiniteSubspace K_sub)).toLinearMap.comp 𝔨.incl.toLinearMap
  diff_eq_lie := fun X v => by
    rfl
  equivariance := hequiv

def iterLieAction
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {F : Type*} [AddCommGroup F] [Module ℂ F]
    (ι : 𝔤 →ₗ⁅ℂ⁆ (F →ₗ[ℂ] F)) (Xs : List 𝔤) (v : F) : F :=
  Xs.foldr (fun X w => (ι X) w) v

end
