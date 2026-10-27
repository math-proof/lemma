import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory AlgebraicGeometry Opposite
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private noncomputable def secMap
  {S : Type} [CommRing S]
  {A : (Scheme : Type 1)}
  (f : A ⟶ Spec (CommRingCat.of S))
  (U : A.Opens) :
  RingHom S (A.presheaf.obj (op U)) :=
  ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appLE ⊤ U le_top).hom

private lemma appLE_SpecMap_comp_fromSpec
  {C : Type} [CommRing C]
  {A : (Scheme : Type 1)}
  {U : A.Opens}
  (q : RingHom (A.presheaf.obj (op U)) C)
  -- given
  (hU : IsAffineOpen U)
  (e : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ (TopologicalSpace.Opens.map (Spec.map (CommRingCat.ofHom q) ≫ hU.fromSpec).base).obj U) :
  -- imply
  (Spec.map (CommRingCat.ofHom q) ≫ hU.fromSpec).appLE U ⊤ e =
    CommRingCat.ofHom q ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).inv := by
  -- proof
  have e₁ : (⊤ : (Spec (A.presheaf.obj (op U))).Opens) ≤ (TopologicalSpace.Opens.map hU.fromSpec.base).obj U := by
    rw [hU.fromSpec_preimage_self]
  have e₂ : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ (TopologicalSpace.Opens.map (Spec.map (CommRingCat.ofHom q)).base).obj ⊤ :=
    fun _ _ => trivial
  rw [← Scheme.Hom.appLE_comp_appLE _ _ U ⊤ ⊤ e₁ e₂]
  have h1 : hU.fromSpec.appLE U ⊤ e₁ = (Scheme.ΓSpecIso (A.presheaf.obj (op U))).inv := by
    simp only [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    have : ((eqToHom hU.fromSpec_preimage_self).op ≫ (homOfLE e₁).op :
        (op ⊤ : (Spec (A.presheaf.obj (op U))).Opensᵒᵖ) ⟶ op ⊤) = 𝟙 _ := Subsingleton.elim _ _
    rw [this, CategoryTheory.Functor.map_id, Category.comp_id]
  have h2 : (Spec.map (CommRingCat.ofHom q)).appLE ⊤ ⊤ e₂ = (Spec.map (CommRingCat.ofHom q)).appTop := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.appTop]
    have : ((homOfLE e₂).op : (op ((TopologicalSpace.Opens.map (Spec.map (CommRingCat.ofHom q)).base).obj ⊤)) ⟶ op ⊤) = 𝟙 _ :=
      Subsingleton.elim _ _
    rw [this]
    erw [CategoryTheory.Functor.map_id]
    erw [Category.comp_id]
  rw [h1, h2, ← Scheme.ΓSpecIso_inv_naturality]

private lemma map_ker_le_of_localTest
  {S : Type} [CommRing S]
  {A : (Scheme : Type 1)}
  (f : A ⟶ Spec (CommRingCat.of S))
  {Z₁ Z₂ : (Scheme : Type 1)}
  (ι₁ : Z₁ ⟶ A) [IsClosedImmersion ι₁]
  (ι₂ : Z₂ ⟶ A) [IsClosedImmersion ι₂]
  (𝔭 : PrimeSpectrum S)
  (U : A.affineOpens)
  (BM : Type) [CommRing BM] [Algebra (A.presheaf.obj (op U.1)) BM] [IsLocalization ((𝔭.asIdeal.primeCompl).map (secMap f U.1).toMonoidHom) BM]
  -- given
  (h : ∀ (R : Type) [CommRing R] (ψ : Spec (CommRingCat.of R) ⟶ A), (∃ t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of (Localization.AtPrime 𝔭.asIdeal)), t ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal))) = ψ ≫ f) → (∃ ψ₁ : Spec (CommRingCat.of R) ⟶ Z₁, ψ₁ ≫ ι₁ = ψ) → (∃ ψ₂ : Spec (CommRingCat.of R) ⟶ Z₂, ψ₂ ≫ ι₂ = ψ)) :
  -- imply
  (ι₂.ker.ideal U).map (algebraMap (A.presheaf.obj (op U.1)) BM) ≤ (ι₁.ker.ideal U).map (algebraMap (A.presheaf.obj (op U.1)) BM) := by
  -- proof
  classical
  have hU : IsAffineOpen U.1 := U.2
  let _ : IsAffine U.1 := hU
  let J₁ : Ideal (A.presheaf.obj (op U.1)) := ι₁.ker.ideal U
  let C : Type := BM ⧸ J₁.map (algebraMap (A.presheaf.obj (op U.1)) BM)
  let q : RingHom (A.presheaf.obj (op U.1)) C := (Ideal.Quotient.mk _).comp (algebraMap (A.presheaf.obj (op U.1)) BM)
  have hqJ : ∀ b ∈ J₁, q b = 0 := fun b hb => (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.mem_map_of_mem _ hb)
  let ψ : Spec (CommRingCat.of C) ⟶ A := Spec.map (CommRingCat.ofHom q) ≫ hU.fromSpec
  let ψU : Spec (CommRingCat.of C) ⟶ U.1 := Spec.map (CommRingCat.ofHom q) ≫ hU.isoSpec.inv
  have hψU : ψU ≫ U.1.ι = ψ := by
    simp only [ψ, ψU, Category.assoc, IsAffineOpen.isoSpec_inv_ι]
  have hover : ∃ t : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of (Localization.AtPrime 𝔭.asIdeal)), t ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal))) = ψ ≫ f := by
    let ℓ : RingHom (Localization.AtPrime 𝔭.asIdeal) BM :=
      IsLocalization.map (M := 𝔭.asIdeal.primeCompl) (T := (𝔭.asIdeal.primeCompl).map (secMap f U.1).toMonoidHom) BM (secMap f U.1) (fun x hx => Submonoid.mem_comap.mpr (Submonoid.mem_map_of_mem (secMap f U.1).toMonoidHom hx))
    refine ⟨Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk _).comp ℓ)), ?_⟩
    have e0 : U.1 ≤ (TopologicalSpace.Opens.map f.base).obj ⊤ := le_top
    rw [← Spec.map_comp]
    change _ = (Spec.map (CommRingCat.ofHom q) ≫ hU.fromSpec) ≫ f
    rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) hU e0, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    change (Ideal.Quotient.mk _) (ℓ (algebraMap S _ x)) = q ((f.appLE ⊤ U.1 e0).hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom x))
    rw [IsLocalization.map_eq]
    rfl
  have hfac₁ : ∃ ψ₁ : Spec (CommRingCat.of C) ⟶ Z₁, ψ₁ ≫ ι₁ = ψ := by
    have H : (morphismRestrict ι₁ U.1).ker ≤ ψU.ker := by
      apply Scheme.IdealSheafData.le_of_isAffine
      rw [Scheme.ker_morphismRestrict_ideal]
      intro b hb
      rw [Scheme.Hom.ker_apply ψU, RingHom.mem_ker]
      have hb' : U.1.topIso.hom b ∈ J₁ := by
        have hm := Scheme.IdealSheafData.map_ideal' ι₁.ker (U := U) (V := ⟨(Scheme.Hom.opensFunctor U.1.ι).obj ⊤, (isAffineOpen_top _).image_of_isOpenImmersion _⟩) (eqToHom U.1.ι_image_top.symm).op
        change (U.1.topIso.hom b) ∈ ι₁.ker.ideal U
        rw [← hm]
        apply Ideal.mem_map_of_mem _ hb
      have happ : ψU.appTop = U.1.topIso.hom ≫ CommRingCat.ofHom q ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).inv := by
        simp only [ψU, Scheme.Hom.comp_appTop, IsAffineOpen.isoSpec_inv_appTop, Category.assoc]
        rw [← Scheme.ΓSpecIso_inv_naturality]
      change ψU.appTop b = 0
      rw [happ]
      change (Scheme.ΓSpecIso (CommRingCat.of C)).inv (q (U.1.topIso.hom b)) = 0
      rw [hqJ _ hb', map_zero]
    refine ⟨IsClosedImmersion.lift (morphismRestrict ι₁ U.1) ψU H ≫ Scheme.Opens.ι ((TopologicalSpace.Opens.map ι₁.base).obj U.1), ?_⟩
    rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc, IsClosedImmersion.lift_fac, hψU]
  obtain ⟨ψ₂, hψ₂⟩ := h C ψ hover hfac₁
  have hker : ι₂.ker ≤ ψ.ker := hψ₂ ▸ Scheme.Hom.le_ker_comp ψ₂ ι₂
  rw [Ideal.map_le_iff_le_comap]
  intro b hb
  rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
  change q b = 0
  have h1 : (ψ.app U.1).hom b = 0 := Scheme.Hom.ideal_ker_le ψ U (Scheme.IdealSheafData.le_def.mp hker U hb)
  have e : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ (TopologicalSpace.Opens.map ψ.base).obj U.1 := by
    change ⊤ ≤ (TopologicalSpace.Opens.map (Spec.map (CommRingCat.ofHom q)).base).obj ((TopologicalSpace.Opens.map hU.fromSpec.base).obj U.1)
    rw [hU.fromSpec_preimage_self]
    intro _ _
    trivial
  have h2 : (ψ.appLE U.1 ⊤ e).hom b = 0 := by
    simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply, h1, map_zero]
  have h3 := appLE_SpecMap_comp_fromSpec q hU e
  change (Spec.map (CommRingCat.ofHom q) ≫ hU.fromSpec).appLE U.1 ⊤ e = _ at h3
  have h4 : (Scheme.ΓSpecIso (CommRingCat.of C)).inv (q b) = 0 := by
    have := congrArg (fun φ => φ.hom b) h3
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    rw [← this]
    apply h2
  refine (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of C)).inv).1).mp h4

private lemma map_ker_eq_of_localTest
  {S : Type} [CommRing S]
  {A : (Scheme : Type 1)}
  (f : A ⟶ Spec (CommRingCat.of S))
  {Z₁ Z₂ : (Scheme : Type 1)}
  (ι₁ : Z₁ ⟶ A) [IsClosedImmersion ι₁]
  (ι₂ : Z₂ ⟶ A) [IsClosedImmersion ι₂]
  (𝔭 : PrimeSpectrum S)
  (U : A.affineOpens)
  (BM : Type) [CommRing BM] [Algebra (A.presheaf.obj (op U.1)) BM] [IsLocalization ((𝔭.asIdeal.primeCompl).map (secMap f U.1).toMonoidHom) BM]
  -- given
  (h : ∀ (R : Type) [CommRing R] (ψ : Spec (CommRingCat.of R) ⟶ A), (∃ t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of (Localization.AtPrime 𝔭.asIdeal)), t ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal))) = ψ ≫ f) → ((∃ ψ₁ : Spec (CommRingCat.of R) ⟶ Z₁, ψ₁ ≫ ι₁ = ψ) ↔ (∃ ψ₂ : Spec (CommRingCat.of R) ⟶ Z₂, ψ₂ ≫ ι₂ = ψ))) :
  -- imply
  (ι₁.ker.ideal U).map (algebraMap (A.presheaf.obj (op U.1)) BM) = (ι₂.ker.ideal U).map (algebraMap (A.presheaf.obj (op U.1)) BM) :=
  le_antisymm (map_ker_le_of_localTest f ι₂ ι₁ 𝔭 U BM (fun R _ ψ hψ => (h R ψ hψ).mpr)) (map_ker_le_of_localTest f ι₁ ι₂ 𝔭 U BM (fun R _ ψ hψ => (h R ψ hψ).mp))

/--
[AlgebraicGeometry_IsClosedImmersion_map_ideal_ker_eq_of_forall_factorsThrough_iff_atPrime](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_IsClosedImmersion_map_ideal_ker_eq_of_forall_factorsThrough_iff_atPrime.lean)
-/
@[path]
private lemma main
  {S : Type} [CommRing S]
  {A : (Scheme : Type 1)}
  (f : A ⟶ Spec (CommRingCat.of S))
  {Z₁ Z₂ : (Scheme : Type 1)}
  (ι₁ : Z₁ ⟶ A) [IsClosedImmersion ι₁]
  (ι₂ : Z₂ ⟶ A) [IsClosedImmersion ι₂]
  (𝔭 : PrimeSpectrum S)
  (V : A.affineOpens)
  (Bₚ : Type) [CommRing Bₚ] [Algebra (A.presheaf.obj (op V.1)) Bₚ] [IsLocalization (𝔭.asIdeal.primeCompl.map (secMap f V.1).toMonoidHom) Bₚ]
  -- given
  (h : ∀ (R : Type) [CommRing R] (ψ : Spec (CommRingCat.of R) ⟶ A), (∃ t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of (Localization.AtPrime 𝔭.asIdeal)), t ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal))) = ψ ≫ f) → ((∃ ψ₁ : Spec (CommRingCat.of R) ⟶ Z₁, ψ₁ ≫ ι₁ = ψ) ↔ (∃ ψ₂ : Spec (CommRingCat.of R) ⟶ Z₂, ψ₂ ≫ ι₂ = ψ))) :
  -- imply
  (ι₁.ker.ideal V).map (algebraMap (A.presheaf.obj (op V.1)) Bₚ) = (ι₂.ker.ideal V).map (algebraMap (A.presheaf.obj (op V.1)) Bₚ) := by
  -- proof
  apply map_ker_eq_of_localTest f ι₁ ι₂ 𝔭 V Bₚ h


-- created on 2026-10-20
