import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

variable {T' T : Type u} [CommRing T'] [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π)
  (A : Type u) [CommRing A] [Algebra T' A]
abbrev J : Ideal A := (RingHom.ker π).map (algebraMap T' A)
private noncomputable def πbar : T →+* A ⧸ J π A :=
  (Ideal.Quotient.lift (RingHom.ker π) ((Ideal.Quotient.mk (J π A)).comp (algebraMap T' A)) (fun x hx => by
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      apply Ideal.mem_map_of_mem _ hx)).comp
    (RingHom.quotientKerEquivOfSurjective hπ).symm.toRingHom
private lemma πbar_apply (x : T') : πbar π hπ A (π x) = Ideal.Quotient.mk (J π A) (algebraMap T' A x) := by
  have : (RingHom.quotientKerEquivOfSurjective hπ).symm (π x) = Ideal.Quotient.mk _ x := by
    apply (RingHom.quotientKerEquivOfSurjective hπ).injective
    rw [RingEquiv.apply_symm_apply, RingHom.quotientKerEquivOfSurjective_apply_mk]
  simp [πbar, this]
private lemma isPushout_quotient :
  IsPushout (CommRingCat.ofHom (algebraMap T' A)) (CommRingCat.ofHom π)
    (CommRingCat.ofHom (Ideal.Quotient.mk (J π A))) (CommRingCat.ofHom (πbar π hπ A)) := by
  have w : CommSq (CommRingCat.ofHom (algebraMap T' A)) (CommRingCat.ofHom π)
    (CommRingCat.ofHom (Ideal.Quotient.mk (J π A))) (CommRingCat.ofHom (πbar π hπ A)) :=
    ⟨by
      ext x
      simp [πbar_apply]⟩
  refine IsPushout.of_isColimit' w (PushoutCocone.IsColimit.mk _ (fun s => ?_) (fun s => ?_) (fun s => ?_) ?_)
  ·
    have hker : J π A ≤ RingHom.ker s.inl.hom := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap, RingHom.mem_ker]
      have := CategoryTheory.congr_fun s.condition x
      simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at this
      rw [RingHom.mem_ker] at hx
      rw [this, hx, map_zero]
    refine CommRingCat.ofHom (Ideal.Quotient.lift _ s.inl.hom fun a ha => hker ha)
  ·
    ext a
    rfl
  ·
    ext t
    obtain ⟨x, rfl⟩ := hπ t
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom, πbar_apply,
      Ideal.Quotient.lift_mk]
    have := CategoryTheory.congr_fun s.condition x
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at this
    apply this
  ·
    intro s m hm₁ hm₂
    ext a
    have := CategoryTheory.congr_fun hm₁ a
    simpa using this
/--
[AlgebraicGeometry_Smooth_exists_lift_comp_eq_of_isPullback_of_isAffine_of_isNilpotent](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Smooth_exists_lift_comp_eq_of_isPullback_of_isAffine_of_isNilpotent.lean)
-/
@[path]
private lemma main
  {T' T : Type u} [CommRing T'] [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π)
  (hker : IsNilpotent (RingHom.ker π))
  {Z V : (Scheme : Type (u + 1))} (qZ : Z ⟶ Spec (CommRingCat.of T')) [IsAffine Z]
  (gZ : V ⟶ Z) (fV : V ⟶ Spec (CommRingCat.of T)) (hgZ : IsPullback gZ fV qZ (Spec.map (CommRingCat.ofHom π)))
  {Y U : (Scheme : Type (u + 1))} (q : Y ⟶ Spec (CommRingCat.of T')) [IsAffine Y] [Smooth q]
  (g : U ⟶ Y) (fU : U ⟶ Spec (CommRingCat.of T)) (hg : IsPullback g fU q (Spec.map (CommRingCat.ofHom π)))
  (h : V ⟶ U) (hh : h ≫ fU = fV) :
  ∃ hZ : Z ⟶ Y, hZ ≫ q = qZ ∧ gZ ≫ hZ = h ≫ g := by
  obtain ⟨φq, hφq⟩ := Spec.map_surjective (Y.isoSpec.inv ≫ q)
  obtain ⟨φZ, hφZ⟩ := Spec.map_surjective (Z.isoSpec.inv ≫ qZ)
  let A : Type u := Y.presheaf.obj (op ⊤)
  let B : Type u := Z.presheaf.obj (op ⊤)
  let _ : Algebra T' A := φq.hom.toAlgebra
  let _ : Algebra T' B := φZ.hom.toAlgebra
  let _ : Smooth (Y.isoSpec.inv ≫ q) := inferInstance
  let _ : Algebra.FormallySmooth T' A := by
    have hsmooth : RingHom.Smooth φq.hom := by
      rw [← HasRingHomProperty.Spec_iff (P := @Smooth)]
      apply hφq.symm ▸ (inferInstance : Smooth (Y.isoSpec.inv ≫ q))
    refine hsmooth.formallySmooth
  have hq1 : q = Y.isoSpec.hom ≫ Spec.map φq := by rw [hφq, Iso.hom_inv_id_assoc]
  have hqZ1 : qZ = Z.isoSpec.hom ≫ Spec.map φZ := by rw [hφZ, Iso.hom_inv_id_assoc]
  have hg₁ : IsPullback (g ≫ Y.isoSpec.hom) fU (Spec.map φq) (Spec.map (CommRingCat.ofHom π)) :=
    hg.of_iso (Iso.refl _) Y.isoSpec (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp [hq1]) (by simp)
  have hgZ₁ : IsPullback (gZ ≫ Z.isoSpec.hom) fV (Spec.map φZ) (Spec.map (CommRingCat.ofHom π)) :=
    hgZ.of_iso (Iso.refl _) Z.isoSpec (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp [hqZ1]) (by simp)
  have hpb := isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_quotient π hπ A)
  have hpbZ := isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_quotient π hπ B)
  have eφ : CommRingCat.ofHom (algebraMap T' A) = φq := rfl
  have eφZ : CommRingCat.ofHom (algebraMap T' B) = φZ := rfl
  rw [eφ] at hpb
  rw [eφZ] at hpbZ
  let εU : U ≅ Spec (CommRingCat.of (A ⧸ J π A)) := hg₁.isoIsPullback _ _ hpb
  let εV : V ≅ Spec (CommRingCat.of (B ⧸ J π B)) := hgZ₁.isoIsPullback _ _ hpbZ
  have hεU₁ : εU.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J π A))) = g ≫ Y.isoSpec.hom :=
    hg₁.isoIsPullback_hom_fst _ _ hpb
  have hεU₂ : εU.hom ≫ Spec.map (CommRingCat.ofHom (πbar π hπ A)) = fU := hg₁.isoIsPullback_hom_snd _ _ hpb
  have hεV₁ : εV.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J π B))) = gZ ≫ Z.isoSpec.hom :=
    hgZ₁.isoIsPullback_hom_fst _ _ hpbZ
  have hεV₂ : εV.hom ≫ Spec.map (CommRingCat.ofHom (πbar π hπ B)) = fV := hgZ₁.isoIsPullback_hom_snd _ _ hpbZ
  obtain ⟨χ, hχ⟩ := Spec.map_surjective (εV.inv ≫ h ≫ εU.hom)
  have hχT : CommRingCat.ofHom (πbar π hπ A) ≫ χ = CommRingCat.ofHom (πbar π hπ B) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hχ, Category.assoc, Category.assoc, hεU₂, hh, ← hεV₂, εV.inv_hom_id_assoc]
  have hχlin : ∀ x : T', χ.hom (algebraMap T' (A ⧸ J π A) x) = algebraMap T' (B ⧸ J π B) x := by
    intro x
    have := congrArg (fun f : CommRingCat.of T ⟶ _ => f.hom (π x)) hχT
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply, πbar_apply] at this
    rwa [← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap]
  let χa : (A ⧸ J π A) →ₐ[T'] (B ⧸ J π B) := { toRingHom := χ.hom, commutes' := hχlin }
  let g₀ : A →ₐ[T'] B ⧸ J π B := χa.comp (Ideal.Quotient.mkₐ T' (J π A))
  have hJ : IsNilpotent (J π B) := by
    obtain ⟨n, hn⟩ := hker
    refine ⟨n, ?_⟩
    show ((RingHom.ker π).map (algebraMap T' B)) ^ n = 0
    rw [← Ideal.map_pow, hn, Ideal.zero_eq_bot, Ideal.map_bot]
    rfl
  obtain ⟨ψ, hψ⟩ := Algebra.FormallySmooth.exists_lift (J π B) hJ g₀
  refine ⟨Z.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ Y.isoSpec.inv, ?_, ?_⟩
  ·
    have h1 : φq ≫ CommRingCat.ofHom ψ.toRingHom = φZ := by
      ext x
      change ψ (algebraMap T' A x) = algebraMap T' B x
      apply ψ.commutes x
    simp only [Category.assoc]
    rw [hq1, Y.isoSpec.inv_hom_id_assoc, ← Spec.map_comp, h1, ← hqZ1]
  ·
    have h2 : CommRingCat.ofHom ψ.toRingHom ≫ CommRingCat.ofHom (Ideal.Quotient.mk (J π B)) =
        CommRingCat.ofHom (Ideal.Quotient.mk (J π A)) ≫ χ := by
      ext a
      change (Ideal.Quotient.mkₐ T' (J π B)).comp ψ a = χa (Ideal.Quotient.mkₐ T' (J π A) a)
      rw [hψ]
      rfl
    rw [← cancel_epi εV.inv, ← cancel_mono Y.isoSpec.hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have lhs : εV.inv ≫ gZ ≫ Z.isoSpec.hom = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J π B))) := by
      rw [← hεV₁, εV.inv_hom_id_assoc]
    have rhs : εV.inv ≫ h ≫ g ≫ Y.isoSpec.hom = Spec.map χ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J π A))) := by
      rw [← hεU₁, hχ]
      simp only [Category.assoc]
    have lhs' := congrArg (· ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom)) lhs
    simp only [Category.assoc] at lhs'
    rw [rhs, lhs', ← Spec.map_comp, ← Spec.map_comp, h2]


-- created on 2026-10-20
