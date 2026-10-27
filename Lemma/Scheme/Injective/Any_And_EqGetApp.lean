import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma ker_pullback_fst_comp
  {X Y₁ Y₂ : (Scheme : Type (u + 1))}
  (i₁ : Y₁ ⟶ X) [IsClosedImmersion i₁]
  (i₂ : Y₂ ⟶ X) [IsClosedImmersion i₂] :
  -- imply
  (pullback.fst i₁ i₂ ≫ i₁).ker = i₁.ker ⊔ i₂.ker := by
  -- proof
  apply le_antisymm
  ·
    set J : X.IdealSheafData := i₁.ker ⊔ i₂.ker
    have h₁ : i₁.ker ≤ J.subschemeι.ker := by
      rw [Scheme.IdealSheafData.ker_subschemeι]
      apply le_sup_left
    have h₂ : i₂.ker ≤ J.subschemeι.ker := by
      rw [Scheme.IdealSheafData.ker_subschemeι]
      apply le_sup_right
    let z : J.subscheme ⟶ pullback i₁ i₂ :=
      pullback.lift (IsClosedImmersion.lift i₁ J.subschemeι h₁) (IsClosedImmersion.lift i₂ J.subschemeι h₂)
        (by rw [IsClosedImmersion.lift_fac, IsClosedImmersion.lift_fac])
    have hz : z ≫ (pullback.fst i₁ i₂ ≫ i₁) = J.subschemeι := by
      rw [← Category.assoc, pullback.lift_fst, IsClosedImmersion.lift_fac]
    calc
      _ ≤ (z ≫ (pullback.fst i₁ i₂ ≫ i₁)).ker := Scheme.Hom.le_ker_comp _ _
      _ = J := by
        rw [hz, Scheme.IdealSheafData.ker_subschemeι]
  ·
    refine sup_le (Scheme.Hom.le_ker_comp _ _) ?_
    rw [pullback.condition]
    apply Scheme.Hom.le_ker_comp _ _

private lemma ker_mul_ker_eq_bot
  {X Y₁ Y₂ : (Scheme : Type (u + 1))} [IsReduced X]
  (i₁ : Y₁ ⟶ X) [IsClosedImmersion i₁]
  (i₂ : Y₂ ⟶ X) [IsClosedImmersion i₂]
  -- given
  (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ) :
  -- imply
  i₁.ker * i₂.ker = ⊥ := by
  -- proof
  rw [← Scheme.IdealSheafData.support_eq_top_iff, Scheme.IdealSheafData.support_mul, eq_top_iff]
  intro x _
  obtain h | h := (Set.eq_univ_iff_forall.mp hcover x)
  · apply Or.inl (i₁.range_subset_ker_support h)
  · apply Or.inr (i₂.range_subset_ker_support h)

/--
[AlgebraicGeometry_IsClosedImmersion_app_injective_and_exists_of_app_pullback_eq_of_isAffineOpen](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_IsClosedImmersion_app_injective_and_exists_of_app_pullback_eq_of_isAffineOpen.lean)
-/
@[path]
private lemma main
  {X Y₁ Y₂ : (Scheme : Type (u + 1))} [IsReduced X]
  (i₁ : Y₁ ⟶ X) [IsClosedImmersion i₁]
  (i₂ : Y₂ ⟶ X) [IsClosedImmersion i₂]
  (U : X.Opens)
  -- given
  (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
  (hU : IsAffineOpen U) :
  -- imply
  Function.Injective (fun f : X.presheaf.obj (op U) => ((i₁.app U) f, (i₂.app U) f)) ∧ ∀ (g₁ : Y₁.presheaf.obj (op ((TopologicalSpace.Opens.map i₁.base).obj U))) (g₂ : Y₂.presheaf.obj (op ((TopologicalSpace.Opens.map i₂.base).obj U))), (pullback i₁ i₂).presheaf.map (eqToHom (by rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition] : (TopologicalSpace.Opens.map (pullback.snd i₁ i₂).base).obj ((TopologicalSpace.Opens.map i₂.base).obj U) = (TopologicalSpace.Opens.map (pullback.fst i₁ i₂).base).obj ((TopologicalSpace.Opens.map i₁.base).obj U))).op ((pullback.fst i₁ i₂).app ((TopologicalSpace.Opens.map i₁.base).obj U) g₁) = (pullback.snd i₁ i₂).app ((TopologicalSpace.Opens.map i₂.base).obj U) g₂ → ∃ f : X.presheaf.obj (op U), (i₁.app U) f = g₁ ∧ (i₂.app U) f = g₂ := by
  -- proof
  have hk₁ : RingHom.ker (i₁.app U).hom = i₁.ker.ideal ⟨U, hU⟩ := (Scheme.Hom.ker_apply i₁ ⟨U, hU⟩).symm
  have hk₂ : RingHom.ker (i₂.app U).hom = i₂.ker.ideal ⟨U, hU⟩ := (Scheme.Hom.ker_apply i₂ ⟨U, hU⟩).symm
  have hkπ : RingHom.ker ((pullback.fst i₁ i₂ ≫ i₁).app U).hom = i₁.ker.ideal ⟨U, hU⟩ ⊔ i₂.ker.ideal ⟨U, hU⟩ := by
    rw [← Scheme.Hom.ker_apply _ ⟨U, hU⟩, ker_pullback_fst_comp, Scheme.IdealSheafData.ideal_sup]
    rfl
  refine ⟨?_, ?_⟩
  ·
    intro f g hfg
    simp only [Prod.mk.injEq] at hfg
    rw [← sub_eq_zero]
    have hmem₁ : f - g ∈ i₁.ker.ideal ⟨U, hU⟩ := by
      rw [← hk₁, RingHom.mem_ker, map_sub, sub_eq_zero]
      apply hfg.1
    have hmem₂ : f - g ∈ i₂.ker.ideal ⟨U, hU⟩ := by
      rw [← hk₂, RingHom.mem_ker, map_sub, sub_eq_zero]
      apply hfg.2
    have hsq : (f - g) * (f - g) ∈ (i₁.ker * i₂.ker).ideal ⟨U, hU⟩ := by
      rw [Scheme.IdealSheafData.ideal_mul]
      apply Ideal.mul_mem_mul hmem₁ hmem₂
    rw [ker_mul_ker_eq_bot i₁ i₂ hcover, Scheme.IdealSheafData.ideal_bot] at hsq
    apply IsReduced.eq_zero _ ⟨2, by rw [pow_two, hsq]⟩
  ·
    intro g₁ g₂ h
    obtain ⟨a₁, rfl⟩ := i₁.app_surjective U hU g₁
    obtain ⟨a₂, rfl⟩ := i₂.app_surjective U hU g₂
    have hpre : (TopologicalSpace.Opens.map (pullback.snd i₁ i₂).base).obj ((TopologicalSpace.Opens.map i₂.base).obj U) =
        (TopologicalSpace.Opens.map (pullback.fst i₁ i₂).base).obj ((TopologicalSpace.Opens.map i₁.base).obj U) := by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition]
    have key : ∀ a : X.presheaf.obj (op U), (pullback i₁ i₂).presheaf.map (eqToHom hpre).op ((pullback.fst i₁ i₂).app ((TopologicalSpace.Opens.map i₁.base).obj U) ((i₁.app U) a)) = (pullback.snd i₁ i₂).app ((TopologicalSpace.Opens.map i₂.base).obj U) ((i₂.app U) a) := by
      intro a
      change ((i₁.app U ≫ (pullback.fst i₁ i₂).app ((TopologicalSpace.Opens.map i₁.base).obj U)) ≫ (pullback i₁ i₂).presheaf.map (eqToHom hpre).op) a = (i₂.app U ≫ (pullback.snd i₁ i₂).app ((TopologicalSpace.Opens.map i₂.base).obj U)) a
      rw [← Scheme.Hom.comp_app, ← Scheme.Hom.comp_app, Scheme.Hom.congr_app (pullback.condition (f := i₁) (g := i₂)).symm U]
    have hF : (pullback.fst i₁ i₂).app ((TopologicalSpace.Opens.map i₁.base).obj U) ((i₁.app U) a₁) =
        (pullback.fst i₁ i₂).app ((TopologicalSpace.Opens.map i₁.base).obj U) ((i₁.app U) a₂) := by
      rw [← key a₂] at h
      let _ : IsIso ((pullback i₁ i₂).presheaf.map (eqToHom hpre).op) := by
        rw [eqToHom_op, eqToHom_map]
        infer_instance
      refine (ConcreteCategory.bijective_of_isIso _).1 h
    have hπ : ((pullback.fst i₁ i₂ ≫ i₁).app U) a₁ = ((pullback.fst i₁ i₂ ≫ i₁).app U) a₂ := by
      rw [Scheme.Hom.comp_app]
      apply hF
    have hdiff : a₁ - a₂ ∈ i₁.ker.ideal ⟨U, hU⟩ ⊔ i₂.ker.ideal ⟨U, hU⟩ := by
      rw [← hkπ, RingHom.mem_ker, map_sub, sub_eq_zero]
      apply hπ
    obtain ⟨u₁, hu₁, u₂, hu₂, hu⟩ := Submodule.mem_sup.mp hdiff
    refine ⟨a₁ - u₁, ?_, ?_⟩
    ·
      rw [map_sub, sub_eq_self]
      apply (RingHom.mem_ker.mp (hk₁ ▸ hu₁ : u₁ ∈ RingHom.ker (i₁.app U).hom))
    ·
      have : a₁ - u₁ = a₂ + u₂ := by
        linear_combination -hu
      rw [this, map_add, add_eq_left]
      apply (RingHom.mem_ker.mp (hk₂ ▸ hu₂ : u₂ ∈ RingHom.ker (i₂.app U).hom))


-- created on 2026-10-20
