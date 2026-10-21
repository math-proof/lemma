import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_Scheme_Modules_nonempty_pullback_basicOpen_iso_of_nonempty_pullback_iso_of_isFractionRing](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_basicOpen_iso_of_nonempty_pullback_iso_of_isFractionRing.lean)
-/
@[path]
private lemma main
  (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
  (KK : Type) [Field KK] [Algebra R KK] [IsFractionRing R KK]
  {X XK : (Scheme : Type 1)} (f : X ⟶ Spec (CommRingCat.of R))
  (fK : XK ⟶ Spec (CommRingCat.of KK)) (gK : XK ⟶ X) (hgK : IsPullback gK fK f (Spec.map (CommRingCat.ofHom (algebraMap R KK))))
  (M M' : X.Modules) (h : Nonempty ((Scheme.Modules.pullback gK).obj M ≅ (Scheme.Modules.pullback gK).obj M')) :
    (∀ x : X, x ∈ X.basicOpen (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ϖ)) ↔ f.base x ≠ IsLocalRing.closedPoint R) ∧ Nonempty ((Scheme.Modules.pullback (X.basicOpen (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ϖ))).ι).obj M ≅ (Scheme.Modules.pullback (X.basicOpen (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ϖ))).ι).obj M') := by
  classical
  have hϖirr : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hϖ
  have hϖ0 : ϖ ≠ 0 := hϖirr.ne_zero
  let _ : IsLocalization.Away ϖ KK := by
    have hle : Submonoid.powers ϖ ≤ nonZeroDivisors R := by
      rintro y ⟨n, rfl⟩
      apply mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n hϖ0)
    refine (IsLocalization.iff_of_le_of_exists_dvd (Submonoid.powers ϖ) (nonZeroDivisors R) hle ?_).mpr inferInstance
    intro m hm
    have hm0 : m ≠ 0 := nonZeroDivisors.ne_zero hm
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hm0 hϖirr
    refine ⟨ϖ ^ n, ⟨n, rfl⟩, ⟨↑u⁻¹, ?_⟩⟩
    rw [hu, mul_assoc, mul_comm (ϖ ^ n), ← mul_assoc, Units.mul_inv, one_mul]
  let ι := Spec.map (CommRingCat.ofHom (algebraMap R KK))
  let hιo : IsOpenImmersion ι := IsOpenImmersion.of_isLocalization ϖ (S := KK)
  let _ : IsOpenImmersion gK := MorphismProperty.of_isPullback hgK.flip hιo
  let r : (Spec (CommRingCat.of R)).presheaf.obj (op ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv ϖ
  have hb : (Spec (CommRingCat.of R)).basicOpen r = PrimeSpectrum.basicOpen (R := (CommRingCat.of R)) ϖ :=
    basicOpen_eq_of_affine (R := CommRingCat.of R) ϖ
  have hU : X.basicOpen (f.appTop r) = ((TopologicalSpace.Opens.map f.base).obj ((Spec (CommRingCat.of R)).basicOpen r)) :=
    (Scheme.preimage_basicOpen f r).symm
  have hbset : ((((TopologicalSpace.Opens.map f.base).obj ((Spec (CommRingCat.of R)).basicOpen r)) : X.Opens) : Set X) = Set.preimage f.base {p | ϖ ∉ p.asIdeal} := by
    rw [hb]
    rfl
  have hmem : ∀ x : X, x ∈ X.basicOpen (f.appTop r) ↔ f.base x ≠ IsLocalRing.closedPoint R := by
    intro x
    rw [hU, ← SetLike.mem_coe, hbset, Set.mem_preimage, Set.mem_ofPred_eq]
    constructor
    ·
      intro hx heq
      apply hx
      rw [heq]
      show ϖ ∈ IsLocalRing.maximalIdeal R
      rw [hϖ]
      apply Ideal.mem_span_singleton_self
    ·
      intro hne hmemϖ
      apply hne
      apply PrimeSpectrum.ext
      show (f.base x).asIdeal = IsLocalRing.maximalIdeal R
      apply ((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le (f.base x).isPrime.ne_top (by rwa [hϖ, Ideal.span_singleton_le_iff_mem])).symm
  refine ⟨hmem, ?_⟩
  obtain ⟨φ⟩ := h
  have hrange : Set.range gK.base = Set.range (X.basicOpen (f.appTop r)).ι.base := by
    rw [Scheme.Opens.range_ι, hU, hbset]
    have h1 : gK = hgK.isoPullback.hom ≫ pullback.fst f ι := (hgK.isoPullback_hom_fst).symm
    have hsurj : Function.Surjective hgK.isoPullback.hom.base := by
      intro y
      refine ⟨hgK.isoPullback.inv.base y, ?_⟩
      rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
      rfl
    rw [h1, Scheme.Hom.comp_base, TopCat.coe_comp, hsurj.range_comp, Scheme.Pullback.range_fst]
    congr 1
    change Set.range (PrimeSpectrum.comap (algebraMap R KK)) = _
    rw [PrimeSpectrum.localization_away_comap_range KK ϖ]
    rfl
  let e := IsOpenImmersion.isoOfRangeEq gK (X.basicOpen (f.appTop r)).ι hrange
  have he : e.inv ≫ gK = (X.basicOpen (f.appTop r)).ι := IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _
  have cmp : ∀ N : X.Modules, (Scheme.Modules.pullback (X.basicOpen (f.appTop r)).ι).obj N ≅ (Scheme.Modules.pullback e.inv).obj ((Scheme.Modules.pullback gK).obj N) := fun N =>
    ((Scheme.Modules.pullbackCongr he.symm).app N).trans (((Scheme.Modules.pullbackComp e.inv gK).app N).symm)
  refine ⟨((cmp M).trans ((Scheme.Modules.pullback e.inv).mapIso φ)).trans (cmp M').symm⟩


-- created on 2026-10-20
