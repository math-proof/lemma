import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory AlgebraicGeometry HomogeneousLocalization TopologicalSpace Opposite
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_Proj_exists_cocycle_basicOpen_eq_inf_of_mem_of_pos](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Proj_exists_cocycle_basicOpen_eq_inf_of_mem_of_pos.lean)
-/
@[path]
private lemma main
  {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]
  {d r : ℕ}
  (F : Fin r → A)
  -- given
  (hd : 0 < d)
  (hF : ∀ i : Fin r, F i ∈ 𝒜 d) :
  -- imply
  ∃ w : ∀ i (_ : Fin r), (Proj 𝒜).presheaf.obj (op (Proj.basicOpen 𝒜 (F i))), (∀ i : Fin r, IsAffineOpen (Proj.basicOpen 𝒜 (F i))) ∧ (∀ i : Fin r, w i i = 1) ∧ (∀ i j k : Fin r, (Proj 𝒜).presheaf.map (homOfLE (inf_le_left : Proj.basicOpen 𝒜 (F i) ⊓ Proj.basicOpen 𝒜 (F j) ≤ Proj.basicOpen 𝒜 (F i))).op (w i k) = (Proj 𝒜).presheaf.map (homOfLE (inf_le_left : Proj.basicOpen 𝒜 (F i) ⊓ Proj.basicOpen 𝒜 (F j) ≤ Proj.basicOpen 𝒜 (F i))).op (w i j) * (Proj 𝒜).presheaf.map (homOfLE (inf_le_right : Proj.basicOpen 𝒜 (F i) ⊓ Proj.basicOpen 𝒜 (F j) ≤ Proj.basicOpen 𝒜 (F j))).op (w j k)) ∧ (∀ i j : Fin r, (Proj 𝒜).basicOpen (w i j) = Proj.basicOpen 𝒜 (F i) ⊓ Proj.basicOpen 𝒜 (F j)) := by
  -- proof
  classical
  have res_res : ∀ {P : (Scheme : Type 1)} {U₁ U₂ U₃ : P.Opens} (h₁ : U₁ ≤ U₂) (h₂ : U₂ ≤ U₃) (x : P.presheaf.obj (op U₃)), P.presheaf.map (homOfLE h₁).op (P.presheaf.map (homOfLE h₂).op x) = P.presheaf.map (homOfLE (h₁.trans h₂)).op x := by
    intro P U₁ U₂ U₃ h₁ h₂ x
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  have res_inj : ∀ {P : (Scheme : Type 1)} {U₁ U₂ : P.Opens} (e : U₁ = U₂) (x y : P.presheaf.obj (op U₂)), P.presheaf.map (homOfLE e.le).op x = P.presheaf.map (homOfLE e.le).op y → x = y := by
    intro P U₁ U₂ e x y h
    subst e
    have : (homOfLE (le_refl U₁)).op = 𝟙 _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
    simpa [this] using h
  let q : ∀ i j : Fin r, Away 𝒜 (F i) := fun i j =>
    Away.mk 𝒜 (hF i) 1 (F j) (by simpa only [one_smul] using hF j)
  have hV : ∀ i : Fin r, IsAffineOpen (Proj.basicOpen 𝒜 (F i)) := fun i =>
    Proj.isAffineOpen_basicOpen 𝒜 (F i) (hF i) hd
  refine ⟨fun i j => Proj.awayToSection 𝒜 (F i) (q i j), hV, ?_, ?_, ?_⟩
  ·
    intro i
    have : q i i = 1 := by
      apply HomogeneousLocalization.val_injective
      rw [HomogeneousLocalization.val_one]
      simp only [q, Away.val_mk]
      rw [← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
      refine ⟨1, by simp⟩
    change Proj.awayToSection 𝒜 (F i) (q i i) = 1
    rw [this, map_one]
  ·
    intro i j k
    apply res_inj (Proj.basicOpen_mul 𝒜 (F i) (F j))
    simp only [map_mul, res_res]
    have h1 := congrArg (fun φ => φ.hom (q i k)) (Proj.awayMap_awayToSection 𝒜 (f := F i) (hF j) (x := F i * F j) rfl)
    have h2 := congrArg (fun φ => φ.hom (q i j)) (Proj.awayMap_awayToSection 𝒜 (f := F i) (hF j) (x := F i * F j) rfl)
    have h3 := congrArg (fun φ => φ.hom (q j k)) (Proj.awayMap_awayToSection 𝒜 (f := F j) (hF i) (x := F i * F j) (mul_comm _ _))
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at h1 h2 h3
    rw [h1.symm, h2.symm, h3.symm, ← map_mul]
    congr 1
    apply HomogeneousLocalization.val_injective
    simp only [q, HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.val_mul, Away.val_mk, Localization.mk_mul]
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp only [OneMemClass.coe_one, Submonoid.coe_mul, one_mul]
    ring
  ·
    intro i j
    have hfrom : (hV i).fromSpec = Spec.map (Proj.awayToSection 𝒜 (F i)) ≫ Proj.awayι 𝒜 (F i) (hF i) hd := by
      rw [← Proj.basicOpenIsoSpec_inv_ι, ← IsAffineOpen.isoSpec_inv_ι, ← Category.assoc]
      congr 1
      rw [← cancel_epi (hV i).isoSpec.hom, Iso.hom_inv_id, IsAffineOpen.isoSpec_hom, ← Category.assoc]
      change 𝟙 _ = Proj.basicOpenToSpec 𝒜 (F i) ≫ _
      rw [← Proj.basicOpenIsoSpec_hom 𝒜 (F i) (hF i) hd, Iso.hom_inv_id]
    have hpre : (TopologicalSpace.Opens.map (hV i).fromSpec.base).obj (Proj.basicOpen 𝒜 (F j)) =
        PrimeSpectrum.basicOpen (Proj.awayToSection 𝒜 (F i) (q i j)) := by
      rw [hfrom, Scheme.Hom.comp_preimage, Proj.awayι_preimage_basicOpen 𝒜 (hF i) hd (hF j) hd]
      have hq : Away.isLocalizationElem (hF i) (hF j) = q i j ^ d := by
        apply HomogeneousLocalization.val_injective
        simp only [q, Away.isLocalizationElem, Away.val_mk, HomogeneousLocalization.val_pow, Localization.mk_pow]
        congr 1
        apply Subtype.ext (by simp [pow_one])
      rw [hq]
      conv_rhs => rw [← PrimeSpectrum.basicOpen_pow _ d hd, ← map_pow]
      ext1
      rfl
    rw [← (hV i).fromSpec_image_basicOpen, ← hpre, Scheme.Hom.image_preimage_eq_opensRange_inf, IsAffineOpen.opensRange_fromSpec]


-- created on 2026-10-20
