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


noncomputable section

set_option autoImplicit false

attribute [local instance 100] LieRing.ofAssociativeRing

set_option maxHeartbeats 800000

open scoped Manifold

open ContinuousRep

/-- olean stub: LieRingModule structure on k-finite subspace (proofs deferred). -/
noncomputable def kFiniteSubspace_lieRingModule
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    (_hadm : π.IsAdmissible K_sub)
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (ι : 𝔤 →ₗ⁅ℂ⁆ (F →ₗ[ℂ] F))
    (hι_stable : ∀ (X : 𝔤) (v : F),
      v ∈ π.kFiniteSubspace K_sub → (ι X) v ∈ π.kFiniteSubspace K_sub) :
    LieRingModule 𝔤 ↥(π.kFiniteSubspace K_sub) :=
  sorry

/-- kFiniteSubspace_lieModule deferred (olean stub; type elaboration too heavy). -/

def kFiniteSubspace_kAction
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G) :
    Representation ℂ K_sub ↥(π.kFiniteSubspace K_sub) where
  toFun k :=
  { toFun := fun ⟨v, hv⟩ =>
      ⟨(π.toMonoidHom k) v,
       ContinuousRep.kFiniteSubspace_stable π K_sub k v hv⟩
    map_add' := fun ⟨v, _⟩ ⟨w, _⟩ => by
      ext; simp [map_add]
    map_smul' := fun c ⟨v, _⟩ => by
      ext; simp [map_smul] }
  map_one' := by
    ext ⟨v, _⟩; simp
  map_mul' := fun k₁ k₂ => by
    ext ⟨v, _⟩; simp

end
