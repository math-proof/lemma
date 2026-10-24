import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_ModularCurve_TateSlots
import Lemma.Definitions.Def_ModularCurve_KatzLevelPCusps
import Lemma.Int.P2MUtil

open HahnSeries
open ModularCurve

/--
[ModularCurve_exists_powerSeries_forall_coeff_mem_span_sub_one_ofPowerSeries_eq_tateToricPoint_mul_sub_tateToricPoint](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_exists_powerSeries_forall_coeff_mem_span_sub_one_ofPowerSeries_eq_tateToricPoint_mul_sub_tateToricPoint.lean)
-/

noncomputable def toricX (R : Type*) [CommRing R] (p : ℕ) (c : Rˣ) : PowerSeries R :=
  PowerSeries.mk fun m =>
    if m = 0 then (c : R) * Ring.inverse (1 - (c : R)) ^ 2
    else (∑ d ∈ m.divisors, if p ∣ d then
            ((m / d : ℕ) : R) * ((c : R) ^ (m / d) + ((c⁻¹ : Rˣ) : R) ^ (m / d)) else 0)
      - 2 * (if p ∣ m then ∑ e ∈ (m / p).divisors, (e : R) else 0)

private lemma  tateToricPoint_fst_coeff {K : Type*} [CommRing K] (p : ℕ) (c : Kˣ) (m : ℕ) :
  (tateToricPoint K p c).1.coeff (m : ℤ) =
    (if m = 0 then (c : K) * Ring.inverse (1 - (c : K)) ^ 2
    else (∑ d ∈ m.divisors, if p ∣ d then
            ((m / d : ℕ) : K) * ((c : K) ^ (m / d) + ((c⁻¹ : Kˣ) : K) ^ (m / d)) else 0)
      - 2 * (if p ∣ m then ∑ e ∈ (m / p).divisors, (e : K) else 0)) := by
  rw [tateToricPoint_fst, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_mk]

private lemma  coeff_tateToricPoint_fst_mul_sub_coeff_mem_span_sub_one
  {K : Type*} [CommRing K] (p : ℕ) (c ζ : Kˣ)
  (hc : IsUnit (1 - (c : K))) (hζc : IsUnit (1 - ((ζ : K) * (c : K)))) (m : ℕ) :
  (tateToricPoint K p (ζ * c)).1.coeff (m : ℤ) - (tateToricPoint K p c).1.coeff (m : ℤ) ∈
    Ideal.span {((ζ : K) - 1)} := by
  classical
  have hpow : ∀ e : ℕ, (ζ : K) ^ e - 1 ∈ Ideal.span {((ζ : K) - 1)} := by
    intro e
    rw [Ideal.mem_span_singleton]
    exact sub_one_dvd_pow_sub_one (ζ : K) e
  have hpow' : ∀ e : ℕ, ((ζ⁻¹ : Kˣ) : K) ^ e - 1 ∈ Ideal.span {((ζ : K) - 1)} := by
    intro e
    have h1 : ((ζ⁻¹ : Kˣ) : K) ^ e - 1 = -(((ζ⁻¹ : Kˣ) : K) ^ e) * ((ζ : K) ^ e - 1) := by
      have hz : ((ζ⁻¹ : Kˣ) : K) ^ e * (ζ : K) ^ e = 1 := by
        rw [← mul_pow, Units.inv_mul, one_pow]
      linear_combination hz
    rw [h1]
    exact Ideal.mul_mem_left _ _ (hpow e)
  rw [tateToricPoint_fst_coeff, tateToricPoint_fst_coeff]
  by_cases hm : m = 0
  ·
    rw [ite_eq_left hm, ite_eq_left hm]
    obtain ⟨u, hu⟩ := hc
    obtain ⟨u', hu'⟩ := hζc
    have hcoe : ((ζ * c : Kˣ) : K) = (ζ : K) * (c : K) := Units.val_mul ζ c
    rw [hcoe, ← hu, ← hu', Ring.inverse_unit, Ring.inverse_unit]
    have key : (ζ : K) * (c : K) * (↑u'⁻¹ : K) ^ 2 - (c : K) * (↑u⁻¹ : K) ^ 2 =
        ((↑u⁻¹ : K) * (↑u'⁻¹ : K)) ^ 2 * (((ζ : K) - 1) * ((c : K) - (ζ : K) * (c : K) ^ 3)) := by
      have e1 : (u : K) * (↑u⁻¹ : K) = 1 := Units.mul_inv u
      have e2 : (u' : K) * (↑u'⁻¹ : K) = 1 := Units.mul_inv u'
      rw [hu] at e1; rw [hu'] at e2
      linear_combination (-((ζ : K) * (c : K) * (↑u'⁻¹ : K) ^ 2 * (1 + (1 - (c : K)) * (↑u⁻¹ : K)))) * e1
        + ((c : K) * (↑u⁻¹ : K) ^ 2 * (1 + (1 - (ζ : K) * (c : K)) * (↑u'⁻¹ : K))) * e2
    rw [key]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  ·
    rw [ite_eq_right hm, ite_eq_right hm, sub_sub_sub_cancel_right, ← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun d _ => ?_
    split_ifs with hpd
    ·
      have hcoe : ((ζ * c : Kˣ) : K) = (ζ : K) * (c : K) := Units.val_mul ζ c
      have hcoe' : (((ζ * c)⁻¹ : Kˣ) : K) = ((ζ⁻¹ : Kˣ) : K) * ((c⁻¹ : Kˣ) : K) := by
        rw [mul_inv, Units.val_mul]
      rw [hcoe, hcoe', ← mul_sub, mul_pow, mul_pow]
      have : ((ζ : K) ^ (m / d) * (c : K) ^ (m / d) + ((ζ⁻¹ : Kˣ) : K) ^ (m / d) * ((c⁻¹ : Kˣ) : K) ^ (m / d)) -
          ((c : K) ^ (m / d) + ((c⁻¹ : Kˣ) : K) ^ (m / d)) =
          ((ζ : K) ^ (m / d) - 1) * (c : K) ^ (m / d) + (((ζ⁻¹ : Kˣ) : K) ^ (m / d) - 1) * ((c⁻¹ : Kˣ) : K) ^ (m / d) := by ring
      rw [this]
      exact Ideal.mul_mem_left _ _ (Ideal.add_mem _ (Ideal.mul_mem_right _ _ (hpow _)) (Ideal.mul_mem_right _ _ (hpow' _)))
    · simp
p2m_open "ModularCurve P2MW.S_ModularCurve_exists_powerSeries_forall_coeff_mem_span_sub_one_ofPowerSeries_eq_tateToricPoint_mul_sub_tateToricPoint.ModularCurve"

private lemma  tateToricPoint_fst_eq (R : Type*) [CommRing R] (p : ℕ) (c : Rˣ) :
  (tateToricPoint R p c).1 = HahnSeries.ofPowerSeries ℤ R (toricX R p c) := rfl

private lemma  map_toricX {A B : Type*} [CommRing A] [CommRing B] (g : A →+* B) (p : ℕ) (c : Aˣ)
  (hc : IsUnit (1 - (c : A))) :
  PowerSeries.map g (toricX A p c) = toricX B p (Units.map (g : A →* B) c) := by
  ext m
  rw [PowerSeries.coeff_map, toricX, toricX, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  by_cases hm : m = 0
  ·
    rw [ite_eq_left hm, ite_eq_left hm, map_mul, map_pow, Units.coe_map, MonoidHom.coe_coe]
    congr 2
    obtain ⟨u, hu⟩ := hc
    rw [← hu, Ring.inverse_unit, show (1 : B) - g (c : A) = ((Units.map (g : A →* B) u : Bˣ) : B) by
      rw [Units.coe_map, MonoidHom.coe_coe, hu, map_sub, map_one], Ring.inverse_unit, Units.coe_map_inv]
    rfl
  ·
    rw [ite_eq_right hm, ite_eq_right hm]
    simp only [map_sub, map_sum, map_mul, map_add, map_pow, map_natCast, apply_ite g, map_zero, map_ofNat,
      Units.coe_map, Units.coe_map_inv, MonoidHom.coe_coe]


@[path]
private lemma main
  [Field L] [CharZero L] [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
  {N : ℕ}
  {c ζ' : Aˣ}
-- given
  (hc : IsUnit (1 - (c : A)))
  (hζ'c : IsUnit (1 - (ζ' : A) * (c : A))) :
-- imply
  ∃ P : PowerSeries A, (∀ n : ℕ, PowerSeries.coeff n P ∈ Ideal.span {((ζ' : A) - 1)}) ∧
      HahnSeries.ofPowerSeries ℤ L (P.map (algebraMap A L)) =
        (ModularCurve.tateToricPoint L N (Units.map (↑(algebraMap A L) : A →* L) (ζ' * c))).1 -
          (ModularCurve.tateToricPoint L N (Units.map (↑(algebraMap A L) : A →* L) c)).1 := by
-- proof
  refine ⟨toricX A N (ζ' * c) - toricX A N c, fun n => ?_, ?_⟩
  ·
    have h := coeff_tateToricPoint_fst_mul_sub_coeff_mem_span_sub_one N c ζ' hc hζ'c n
    rw [tateToricPoint_fst_eq, tateToricPoint_fst_eq, HahnSeries.ofPowerSeries_apply_coeff,
      HahnSeries.ofPowerSeries_apply_coeff] at h
    rwa [map_sub]
  ·
    have hζ'c' : IsUnit (1 - ((ζ' * c : Aˣ) : A)) := by rwa [Units.val_mul]
    rw [map_sub, map_sub, map_toricX _ N (ζ' * c) hζ'c', map_toricX _ N c hc, ← tateToricPoint_fst_eq, ← tateToricPoint_fst_eq]


-- created on 2026-10-23
