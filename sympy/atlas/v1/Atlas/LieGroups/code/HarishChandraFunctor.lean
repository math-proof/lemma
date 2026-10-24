/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HarishChandraFunctor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.LieGroups.code.Admissible
import Lemma.Bijective.EqContinuousLinearEquivOfBijective.of.Bijective
import Lemma.Real.GetToMonoidHom.in.SmoothSubspace.of.In_SmoothSubspace
import Lemma.Complex.inner.of.IsUnitary
import sympy.atlas.v1.Atlas.LieGroups.code.GKModule
import sympy.atlas.v1.Atlas.LieGroups.code.GKModuleDefs
import sympy.atlas.v1.Atlas.LieGroups.code.SmoothVectors
import sympy.atlas.v1.Atlas.LieGroups.code.KFiniteProps

noncomputable section

set_option autoImplicit false

open scoped Manifold

@[reducible]
def kFiniteSubspace_lieRingModule
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
  letI : Bracket 𝔤 ↥(π.kFiniteSubspace K_sub) :=
    ⟨fun X v => ⟨(ι X) v.val, hι_stable X v.val v.prop⟩⟩
  { add_lie := fun x y m => by
      apply Subtype.ext
      show (ι (x + y)) m.val = (ι x) m.val + (ι y) m.val
      simp [map_add, LinearMap.add_apply]
    lie_add := fun x m n => by
      apply Subtype.ext
      show (ι x) (m.val + n.val) = (ι x) m.val + (ι x) n.val
      simp [map_add]
    leibniz_lie := fun x y m => by
      apply Subtype.ext
      show (ι x) ((ι y) m.val) = (ι ⁅x, y⁆) m.val + (ι y) ((ι x) m.val)
      rw [ι.map_lie x y, Ring.lie_def]; simp [LinearMap.sub_apply] }

@[reducible]
def kFiniteSubspace_lieModule
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
    @LieModule ℂ 𝔤 ↥(π.kFiniteSubspace K_sub) _ _ _ _ _
      (kFiniteSubspace_lieRingModule I π K_sub _hadm 𝔤 ι hι_stable) :=
  @LieModule.mk ℂ 𝔤 ↥(π.kFiniteSubspace K_sub) _ _ _ _ _
    (kFiniteSubspace_lieRingModule I π K_sub _hadm 𝔤 ι hι_stable)
    (fun t x m => by
      apply Subtype.ext
      show (ι (t • x)) m.val = t • ((ι x) m.val)
      simp [map_smul, LinearMap.smul_apply])
    (fun t x m => by
      apply Subtype.ext
      show (ι x) (t • m.val) = t • ((ι x) m.val)
      simp [map_smul])

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
  intro ⟨v, hv⟩


  set σ := kFiniteSubspace_kAction π K_sub
  set S_VK := Submodule.span ℂ (Set.range (fun k : K_sub => σ k ⟨v, hv⟩))
  set S_F := Submodule.span ℂ (Set.range (fun k : K_sub => (π.toMonoidHom k) v))

  have hmap : S_VK.map (π.kFiniteSubspace K_sub).subtype ≤ S_F := by
    rw [Submodule.map_span]
    apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨⟨w, hw⟩, hk, rfl⟩ := hx
    obtain ⟨k, hk'⟩ := hk
    simp only [Submodule.subtype_apply]
    have : w = (π.toMonoidHom k) v := (congr_arg Subtype.val hk').symm
    rw [this]
    exact Submodule.subset_span ⟨k, rfl⟩

  haveI : FiniteDimensional ℂ S_F := hv

  haveI : FiniteDimensional ℂ (S_VK.map (π.kFiniteSubspace K_sub).subtype) :=
    Module.Finite.of_injective (Submodule.inclusion hmap) (Submodule.inclusion_injective hmap)

  exact Module.Finite.of_injective
    (Submodule.equivMapOfInjective _ (Submodule.injective_subtype _) S_VK).toLinearMap
    (LinearEquiv.injective _)

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
  rw [ContinuousRep.mem_kFiniteSubspace] at hv ⊢
  unfold ContinuousRep.IsKFinite at *

  have hsub : Submodule.span ℂ
      (Set.range (fun k : K_sub => (π₂.toMonoidHom k) (T.toContinuousLinearMap v))) ≤
      (Submodule.span ℂ (Set.range (fun k : K_sub => (π₁.toMonoidHom k) v))).map
        T.toContinuousLinearMap.toLinearMap := by
    apply Submodule.span_le.mpr
    intro x hx; obtain ⟨k, rfl⟩ := hx

    dsimp only
    have hintertwine := T.intertwines (k : G)
    have heq : (π₂.toMonoidHom ↑k) (T.toContinuousLinearMap v) =
        T.toContinuousLinearMap ((π₁.toMonoidHom ↑k) v) := by
      have := ContinuousLinearMap.ext_iff.mp hintertwine v
      simp [ContinuousLinearMap.comp_apply] at this
      exact this.symm
    rw [heq]
    exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨k, rfl⟩)
  haveI : FiniteDimensional ℂ
      (Submodule.span ℂ (Set.range (fun k : K_sub => (π₁.toMonoidHom k) v))) := hv
  haveI : FiniteDimensional ℂ
      ((Submodule.span ℂ (Set.range (fun k : K_sub => (π₁.toMonoidHom k) v))).map
        T.toContinuousLinearMap.toLinearMap) :=
    inferInstance
  exact Module.Finite.of_injective
    (Submodule.inclusion hsub) (Submodule.inclusion_injective hsub)

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
    simp [map_add]
  map_smul' c v := by
    apply Subtype.ext
    simp [map_smul]

structure UnitaryRepEquiv
    {G : Type*} [Group G] [TopologicalSpace G]
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    (π₁ : ContinuousRep G V) (π₂ : ContinuousRep G W) extends RepEquiv π₁ π₂ where
  inner_preserving : ∀ (v w : V),
    @inner ℂ W _ (toContinuousLinearEquiv v) (toContinuousLinearEquiv w) =
    @inner ℂ V _ v w

end
