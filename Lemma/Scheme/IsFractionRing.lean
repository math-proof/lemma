import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma isFractionRing_of_localization_iso
  {R S R' S' : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
  [CommRing R'] [CommRing S'] [Nontrivial S'] [Algebra R R'] (M : Submonoid R) [IsLocalization M R']
  (φ : RingHom R S) (β : RingHom S S') (hβ : Function.Injective β) (e : RingEquiv R' S')
  (he : ∀ r, e (algebraMap R R' r) = β (φ r)) :
    let _ : Algebra R (FractionRing S) := ((algebraMap S (FractionRing S)).comp φ).toAlgebra
    IsFractionRing R (FractionRing S) := by
  let _ : Algebra R (FractionRing S) := ((algebraMap S (FractionRing S)).comp φ).toAlgebra
  have hM0 : ∀ m : M, (m : R) ≠ 0 := by
    intro m hm
    have hu : IsUnit (algebraMap R R' m) := IsLocalization.map_units R' m
    rw [hm, map_zero, isUnit_zero_iff] at hu
    have : (0 : S') = 1 := by rw [← map_zero e, hu, map_one]
    exact zero_ne_one this
  have hinj : Function.Injective φ := by
    intro a b hab
    rw [← sub_eq_zero] at hab ⊢
    have h1 : algebraMap R R' (a - b) = 0 := by
      apply e.injective
      rw [he, map_sub φ, hab, map_zero, map_zero]
    obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff M R' (a - b)).mp h1
    obtain h | h := mul_eq_zero.mp hm
    · apply absurd h (hM0 m)
    · apply h
  have hkey : ∀ s : S, ∃ r : R, ∃ m : M, s * φ m = φ r := by
    intro s
    obtain ⟨⟨r, m⟩, hrm⟩ := IsLocalization.surj M (e.symm (β s))
    refine ⟨r, m, hβ ?_⟩
    rw [map_mul, ← he, ← he, ← hrm, map_mul, RingEquiv.apply_symm_apply]
  have halg : ∀ r, algebraMap R (FractionRing S) r = algebraMap S (FractionRing S) (φ r) := fun _ => rfl
  let _ : FaithfulSMul R (FractionRing S) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b hab
    rw [halg, halg] at hab
    exact hinj (IsFractionRing.injective S (FractionRing S) hab)
  apply IsFractionRing.of_field
  intro z
  obtain ⟨s, t, ht, rfl⟩ := IsFractionRing.div_surjective (A := S) z
  obtain ⟨r₁, m₁, h₁⟩ := hkey s
  obtain ⟨r₂, m₂, h₂⟩ := hkey t
  have hm₁ : algebraMap S (FractionRing S) (φ m₁) ≠ 0 := fun h0 =>
    hM0 m₁ (hinj ((IsFractionRing.injective S (FractionRing S) (h0.trans (map_zero _).symm)).trans
      (map_zero φ).symm))
  have hm₂ : algebraMap S (FractionRing S) (φ m₂) ≠ 0 := fun h0 =>
    hM0 m₂ (hinj ((IsFractionRing.injective S (FractionRing S) (h0.trans (map_zero _).symm)).trans
      (map_zero φ).symm))
  have hs : algebraMap S (FractionRing S) s =
      algebraMap S (FractionRing S) (φ r₁) / algebraMap S (FractionRing S) (φ m₁) := by
    rw [eq_div_iff hm₁, ← map_mul, h₁]
  have ht' : algebraMap S (FractionRing S) t =
      algebraMap S (FractionRing S) (φ r₂) / algebraMap S (FractionRing S) (φ m₂) := by
    rw [eq_div_iff hm₂, ← map_mul, h₂]
  refine ⟨r₁ * m₂, m₁ * r₂, ?_⟩
  rw [halg, halg, hs, ht', map_mul, map_mul, map_mul, map_mul, div_div_eq_mul_div, div_mul_eq_mul_div,
    div_div]
private lemma exists_isLocalization_stalkSpecializes
  {X : (Scheme : Type (u + 1))} {x y : X} (h : x ⤳ y) :
    let _ : Algebra (X.presheaf.stalk y) (X.presheaf.stalk x) := (X.presheaf.stalkSpecializes h).hom.toAlgebra
    ∃ M : Submonoid (X.presheaf.stalk y), IsLocalization M (X.presheaf.stalk x) := by
  let iyx : Algebra (X.presheaf.stalk y) (X.presheaf.stalk x) := (X.presheaf.stalkSpecializes h).hom.toAlgebra
  obtain ⟨V, hV, hyV⟩ : ∃ V : X.Opens, IsAffineOpen V ∧ y ∈ V :=
    ⟨(X.affineCover.f (X.affineCover.idx y)).opensRange, isAffineOpen_opensRange _, X.affineCover.covers y⟩
  have hxV : x ∈ V := h.mem_open V.2 hyV
  let ay : Algebra (X.presheaf.obj (op V)) (X.presheaf.stalk y) := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨y, hyV⟩
  let ax : Algebra (X.presheaf.obj (op V)) (X.presheaf.stalk x) := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxV⟩
  let _ : IsScalarTower (X.presheaf.obj (op V)) (X.presheaf.stalk y) (X.presheaf.stalk x) := by
    apply IsScalarTower.of_algebraMap_eq'
    show (X.presheaf.germ V x hxV).hom = (X.presheaf.stalkSpecializes h).hom.comp (X.presheaf.germ V y hyV).hom
    rw [← CommRingCat.hom_comp, TopCat.Presheaf.germ_stalkSpecializes]
  have hLy : IsLocalization.AtPrime (X.presheaf.stalk y) (hV.primeIdealOf ⟨y, hyV⟩).asIdeal :=
    hV.isLocalization_stalk ⟨y, hyV⟩
  have hLx : IsLocalization.AtPrime (X.presheaf.stalk x) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal :=
    hV.isLocalization_stalk ⟨x, hxV⟩
  have hle : hV.primeIdealOf ⟨x, hxV⟩ ≤ hV.primeIdealOf ⟨y, hyV⟩ := by
    rw [PrimeSpectrum.le_iff_specializes]
    exact ((V.isOpenEmbedding'.isInducing.specializes_iff).mp
      (show ((⟨x, hxV⟩ : V) : X) ⤳ ((⟨y, hyV⟩ : V) : X) from h)).map hV.isoSpec.hom.base.hom.continuous
  have hcompl : (hV.primeIdealOf ⟨y, hyV⟩).asIdeal.primeCompl ≤ (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl :=
    fun a ha hax => ha (hle hax)
  refine ⟨_, IsLocalization.isLocalization_of_submonoid_le (X.presheaf.stalk y) (X.presheaf.stalk x) _ _ hcompl⟩
/--
[AlgebraicGeometry_isFractionRing_stalk_fractionRing_stalk_of_isOpenImmersion_restrict](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_isFractionRing_stalk_fractionRing_stalk_of_isOpenImmersion_restrict.lean)
-/
@[path]
private lemma main
  {U W : (Scheme : Type (u + 1))} (v : U ⟶ W) (u : U)
    [IsDomain (U.presheaf.stalk u)] [IsDomain (W.presheaf.stalk (v.base u))]
    (U' : U.Opens) [IsOpenImmersion (U'.ι ≫ v)] (hU' : ∃ x : U, x ∈ U' ∧ x ⤳ u) :
    let _ : Algebra (W.presheaf.stalk (v.base u)) (FractionRing (U.presheaf.stalk u)) :=
      ((algebraMap (U.presheaf.stalk u) (FractionRing (U.presheaf.stalk u))).comp (v.stalkMap u).hom).toAlgebra
    IsFractionRing (W.presheaf.stalk (v.base u)) (FractionRing (U.presheaf.stalk u)) := by
  let _ : Algebra (W.presheaf.stalk (v.base u)) (FractionRing (U.presheaf.stalk u)) :=
    ((algebraMap (U.presheaf.stalk u) (FractionRing (U.presheaf.stalk u))).comp (v.stalkMap u).hom).toAlgebra
  obtain ⟨x, hx, hxu⟩ := hU'
  have hvxu : v.base x ⤳ v.base u := v.base.hom.map_specializes hxu
  let _ : IsIso (v.stalkMap x) := by
    have hc : (U'.ι ≫ v).stalkMap ⟨x, hx⟩ = v.stalkMap x ≫ U'.ι.stalkMap ⟨x, hx⟩ :=
      Scheme.Hom.stalkMap_comp U'.ι v ⟨x, hx⟩
    let i1 : IsIso ((U'.ι ≫ v).stalkMap ⟨x, hx⟩) :=
      (IsOpenImmersion.iff_isIso_stalkMap.mp ‹IsOpenImmersion (U'.ι ≫ v)›).2 ⟨x, hx⟩
    let i2 : IsIso (U'.ι.stalkMap ⟨x, hx⟩) :=
      (IsOpenImmersion.iff_isIso_stalkMap.mp (inferInstance : IsOpenImmersion U'.ι)).2 ⟨x, hx⟩
    have i3 : IsIso (v.stalkMap x ≫ U'.ι.stalkMap ⟨x, hx⟩) := by
      rwa [← hc]
    refine @IsIso.of_isIso_comp_right _ _ _ _ _ (v.stalkMap x) (U'.ι.stalkMap ⟨x, hx⟩) i2 i3
  let aW : Algebra (W.presheaf.stalk (v.base u)) (W.presheaf.stalk (v.base x)) :=
    (W.presheaf.stalkSpecializes hvxu).hom.toAlgebra
  let aU : Algebra (U.presheaf.stalk u) (U.presheaf.stalk x) := (U.presheaf.stalkSpecializes hxu).hom.toAlgebra
  obtain ⟨M, hM⟩ := exists_isLocalization_stalkSpecializes (X := W) hvxu
  obtain ⟨N, hN⟩ := exists_isLocalization_stalkSpecializes (X := U) hxu
  have hN0 : N ≤ nonZeroDivisors (U.presheaf.stalk u) := by
    intro n hn
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro h0
    have hu' : IsUnit (algebraMap (U.presheaf.stalk u) (U.presheaf.stalk x) n) :=
      IsLocalization.map_units (M := N) (U.presheaf.stalk x) ⟨n, hn⟩
    rw [h0, map_zero, isUnit_zero_iff] at hu'
    exact zero_ne_one hu'
  have hβ : Function.Injective (U.presheaf.stalkSpecializes hxu).hom :=
    IsLocalization.injective (M := N) (U.presheaf.stalk x) hN0
  refine isFractionRing_of_localization_iso M (v.stalkMap u).hom (U.presheaf.stalkSpecializes hxu).hom hβ
    (asIso (v.stalkMap x)).commRingCatIsoToRingEquiv ?_
  intro r
  show (W.presheaf.stalkSpecializes hvxu ≫ v.stalkMap x).hom r =
    (v.stalkMap u ≫ U.presheaf.stalkSpecializes hxu).hom r
  rw [Scheme.Hom.stalkSpecializes_stalkMap]


-- created on 2026-10-20
