import Mathlib
import Initialize.Tactic.Attr.Basic
import Structure.v1.Atlas.ArithmeticGeometry.code.CompletenessValuationCriterion.Part2
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.CompletenessValuationCriterion
open AlgebraicGeometry.CompletenessValuationCriterion


/--
[lemma_16_30](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ValuationResidue.lean)
-/
@[path]
lemma lemma_16_30
  {k : Type u}
  [Field k]
  [IsAlgClosed k]
  {F : Type u}
  [Field F]
  {ι : k →+* F}
  {R : ValuationSubring F}
-- given
  (_hι : Function.Injective ι)
  (hkR : ∀ x : k, ι x ∈ R) :
-- imply
  ∃ (R' : ValuationSubring F), (R' ≤ R) ∧ (∀ x : k, ι x ∈ R') ∧ ∃ (Φ : R' →+* k), (RingHom.ker Φ = IsLocalRing.maximalIdeal R') ∧ Function.Surjective Φ := by
-- proof
  set K := IsLocalRing.ResidueField R
  set Ψ : R →+* K := IsLocalRing.residue R
  let ιR : k →+* R := RingHom.codRestrict ι R.toSubring hkR
  let ιK : k →+* K := Ψ.comp ιR
  have hιK_inj : Function.Injective ιK := RingHom.injective ιK
  set A := ιK.range
  let ιK_equiv : k ≃+* A := RingEquiv.ofBijective ιK.rangeRestrict
    ⟨fun a b h => hιK_inj (Subtype.ext_iff.mp h), ιK.rangeRestrict_surjective⟩
  let φ : A →+* k := ιK_equiv.symm.toRingHom
  obtain ⟨S, hAS, Φ_S, _, hker, hsurj⟩ := lemma_16_29 A φ
  let R'_sub : Subring F := (S.toSubring.comap Ψ).map R.subtype
  have mem_iff : ∀ x : F, x ∈ R'_sub ↔
    ∃ h : x ∈ (R : Set F), (Ψ ⟨x, h⟩ : K) ∈ (S : Set K) := by
    intro x; constructor
    · rintro ⟨r, hr_mem, hr_eq⟩; subst hr_eq; exact ⟨r.2, hr_mem⟩
    · rintro ⟨hxR, hxS⟩; exact ⟨⟨x, hxR⟩, hxS, rfl⟩
  have hval : ∀ x : F, x ∈ R'_sub ∨ x⁻¹ ∈ R'_sub := by
    intro x
    by_cases hxR : x ∈ (R : Set F)
    ·
      by_cases hxS : (Ψ ⟨x, hxR⟩ : K) ∈ (S : Set K)
      ·
        left; rw [mem_iff]; exact ⟨hxR, hxS⟩
      ·
        right
        have hΨx_inv_S := (S.mem_or_inv_mem (Ψ ⟨x, hxR⟩)).resolve_left hxS
        have hΨx_ne : Ψ ⟨x, hxR⟩ ≠ 0 := fun h => hxS (h ▸ S.toSubring.zero_mem)
        have hx_not_m : (⟨x, hxR⟩ : R) ∉ IsLocalRing.maximalIdeal R :=
          fun hm => hΨx_ne (Ideal.Quotient.eq_zero_iff_mem.mpr hm)
        have hx_unit : IsUnit (⟨x, hxR⟩ : R) := by
          rw [IsLocalRing.mem_maximalIdeal] at hx_not_m; exact not_not.mp hx_not_m
        have hx_ne : x ≠ 0 := fun h =>
          hx_not_m ((IsLocalRing.mem_maximalIdeal _).mpr (h ▸ not_isUnit_zero))
        have hx_inv_R : x⁻¹ ∈ (R : Set F) := by
          obtain ⟨u, hu⟩ := hx_unit
          suffices (x : F)⁻¹ = ((↑(u⁻¹) : R) : F) from this ▸ (↑(u⁻¹) : R).2
          have h1 : ((u : R) : F) * ((↑(u⁻¹) : R) : F) = 1 :=
            by exact_mod_cast congr_arg Subtype.val (Units.mul_inv u)
          rw [show x = ((u : R) : F) from by
            have := congr_arg Subtype.val hu; simp at this; exact this.symm]
          exact (eq_inv_of_mul_eq_one_right h1).symm
        have hΨ_inv : Ψ ⟨x⁻¹, hx_inv_R⟩ = (Ψ ⟨x, hxR⟩)⁻¹ :=
          eq_inv_of_mul_eq_one_right (by
            rw [← map_mul]; convert map_one Ψ using 2
            ext; simp [mul_inv_cancel₀ hx_ne])
        rw [mem_iff]; exact ⟨hx_inv_R, hΨ_inv ▸ hΨx_inv_S⟩
    ·
      right
      have hx_inv_R := (R.mem_or_inv_mem x).resolve_left hxR
      have hinv_nu := R.inv_mem_nonunits_iff.mpr (Or.inr hxR)
      have hx_inv_m : (⟨x⁻¹, hx_inv_R⟩ : R) ∈ IsLocalRing.maximalIdeal R := by
        rw [IsLocalRing.mem_maximalIdeal]; intro hu
        exact absurd (show R.valuation x⁻¹ = 1 by rwa [R.valuation_eq_one_iff] at hu)
          (ne_of_lt (R.mem_nonunits_iff.mp hinv_nu))
      rw [mem_iff]
      exact ⟨hx_inv_R, (Ideal.Quotient.eq_zero_iff_mem.mpr hx_inv_m) ▸ S.toSubring.zero_mem⟩
  let R' : ValuationSubring F := ValuationSubring.ofSubring R'_sub hval
  have hle : R' ≤ R := fun x hx =>
    ((mem_iff x).mp ((ValuationSubring.mem_ofSubring ..).mp hx)).choose
  have h_img : ∀ r : R', (Ψ (ValuationSubring.inclusion R' R hle r) : K) ∈ (S : Set K) := by
    intro r
    have ⟨_, hS⟩ := (mem_iff (r : F)).mp ((ValuationSubring.mem_ofSubring ..).mp r.2)
    convert hS using 2
  let toS : R' →+* S :=
    (Ψ.comp (ValuationSubring.inclusion R' R hle)).codRestrict S.toSubring h_img
  let Φ : R' →+* k := Φ_S.comp toS
  have hΦ_surj : Function.Surjective Φ := by
    intro y
    obtain ⟨s, hs⟩ := hsurj y
    obtain ⟨r, hr⟩ := IsLocalRing.residue_surjective (s : K)
    have hr_in_R' : (r : F) ∈ R' := by
      rw [ValuationSubring.mem_ofSubring, mem_iff]; exact ⟨r.2, hr ▸ s.2⟩
    exact ⟨⟨(r : F), hr_in_R'⟩, by
      show Φ_S (toS ⟨(r : F), hr_in_R'⟩) = y
      have : toS ⟨(r : F), hr_in_R'⟩ = s := Subtype.ext (by
        show Ψ (ValuationSubring.inclusion R' R hle ⟨(r : F), hr_in_R'⟩) = (s : K)
        simp [ValuationSubring.inclusion]; convert hr using 2)
      rw [this, hs]⟩
  refine ⟨R', hle, ?_, Φ, ?_, hΦ_surj⟩
  ·
    intro x; rw [ValuationSubring.mem_ofSubring, mem_iff]
    exact ⟨hkR x, hAS (RingHom.mem_range_self ιK x)⟩
  ·
    exact IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective Φ hΦ_surj)


-- created on 2026-10-23
