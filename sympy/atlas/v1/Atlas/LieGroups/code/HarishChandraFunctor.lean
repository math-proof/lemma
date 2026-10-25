/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HarishChandraFunctor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.LieGroups.code.Admissible
import Mathlib.Algebra.Lie.OfAssociative
import sympy.atlas.v1.Atlas.LieGroups.code.ContinuousRep
import Lemma.Bijective.EqContinuousLinearEquivOfBijective.of.Bijective
import Lemma.Real.GetToMonoidHom.in.SmoothSubspace.of.In_SmoothSubspace
import sympy.atlas.v1.Atlas.LieGroups.code.GKModule
import sympy.atlas.v1.Atlas.LieGroups.code.GKModuleDefs
import sympy.atlas.v1.Atlas.LieGroups.code.SmoothVectors
import sympy.atlas.v1.Atlas.LieGroups.code.KFiniteProps

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

theorem kFiniteSubspace_kAction_locallyFinite
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G) :
    (kFiniteSubspace_kAction π K_sub).IsLocallyFinite := by
  sorry

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

structure UnitaryRepEquiv
    {G : Type*} [Group G] [TopologicalSpace G]
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    (π₁ : ContinuousRep G V) (π₂ : ContinuousRep G W) extends RepEquiv π₁ π₂ where
  inner_preserving : ∀ (v w : V),
    @inner ℂ W _ (toContinuousLinearEquiv v) (toContinuousLinearEquiv w) =
    @inner ℂ V _ v w

end
