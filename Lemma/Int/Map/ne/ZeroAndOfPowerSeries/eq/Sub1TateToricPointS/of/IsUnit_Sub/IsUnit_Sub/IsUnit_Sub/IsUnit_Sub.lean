import Mathlib
import sympy.Basic
import Lemma.ModularCurve.TateSlots
import Lemma.ModularCurve.KatzLevelPCusps
import Lemma.Int.P2MUtil

open HahnSeries
open ModularCurve

/--
[ModularCurve_exists_powerSeries_map_residue_ne_zero_ofPowerSeries_eq_tateToricPoint_sub_tateToricPoint_sq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_exists_powerSeries_map_residue_ne_zero_ofPowerSeries_eq_tateToricPoint_sub_tateToricPoint_sq.lean)
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

private lemma  isUnit_coeff_zero_tateToricPoint_fst_sub
  {K : Type*} [CommRing K] (p : ℕ) (c c' : Kˣ)
  (hc : IsUnit (1 - (c : K))) (hc' : IsUnit (1 - (c' : K)))
  (hsub : IsUnit ((c : K) - (c' : K))) (hmul : IsUnit (1 - (c : K) * (c' : K))) :
  IsUnit ((tateToricPoint K p c).1.coeff (0 : ℤ) - (tateToricPoint K p c').1.coeff (0 : ℤ)) := by
  have h0 : ((0 : ℕ) : ℤ) = 0 := rfl
  rw [← h0, tateToricPoint_fst_coeff, tateToricPoint_fst_coeff]
  simp only [if_true]
  obtain ⟨u, hu⟩ := hc
  obtain ⟨u', hu'⟩ := hc'
  rw [← hu, ← hu', Ring.inverse_unit, Ring.inverse_unit]
  have key : (c : K) * (↑u⁻¹ : K) ^ 2 - (c' : K) * (↑u'⁻¹ : K) ^ 2 =
      ((↑u⁻¹ : K) * (↑u'⁻¹ : K)) ^ 2 * (((c : K) - (c' : K)) * (1 - (c : K) * (c' : K))) := by
    have e1 : (u : K) * (↑u⁻¹ : K) = 1 := Units.mul_inv u
    have e2 : (u' : K) * (↑u'⁻¹ : K) = 1 := Units.mul_inv u'
    rw [hu] at e1; rw [hu'] at e2
    linear_combination ((c' : K) * (↑u'⁻¹ : K) ^ 2 * (1 + (1 - (c : K)) * (↑u⁻¹ : K))) * e1
      + (-((c : K) * (↑u⁻¹ : K) ^ 2 * (1 + (1 - (c' : K)) * (↑u'⁻¹ : K)))) * e2
  rw [key]
  exact (((Units.isUnit _).mul (Units.isUnit _)).pow 2).mul (hsub.mul hmul)
p2m_open "ModularCurve P2MW.S_ModularCurve_exists_powerSeries_map_residue_ne_zero_ofPowerSeries_eq_tateToricPoint_sub_tateToricPoint_sq.ModularCurve"

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
  {c : Aˣ}
-- given
  (hc : IsUnit (1 - (c : A)))
  (hc2 : IsUnit (1 - (c : A) ^ 2))
  (hcc : IsUnit ((c : A) - (c : A) ^ 2))
  (hc3 : IsUnit (1 - (c : A) ^ 3)) :
-- imply
  ∃ P : PowerSeries A, P.map (IsLocalRing.residue A) ≠ 0 ∧
      HahnSeries.ofPowerSeries ℤ L (P.map (algebraMap A L)) =
        (ModularCurve.tateToricPoint L N (Units.map (↑(algebraMap A L) : A →* L) c)).1 -
          (ModularCurve.tateToricPoint L N (Units.map (↑(algebraMap A L) : A →* L) (c ^ 2))).1 := by
  have hc2' : IsUnit (1 - ((c ^ 2 : Aˣ) : A)) := by rwa [Units.val_pow_eq_pow_val]
  refine ⟨toricX A N c - toricX A N (c ^ 2), ?_, ?_⟩
  ·
    intro h0
    have hcoef := congrArg (PowerSeries.coeff 0) h0
    rw [PowerSeries.coeff_map, map_sub, map_zero] at hcoef
    have hu : IsUnit ((tateToricPoint A N c).1.coeff (0 : ℤ) - (tateToricPoint A N (c ^ 2)).1.coeff (0 : ℤ)) := by
-- proof
      refine isUnit_coeff_zero_tateToricPoint_fst_sub N c (c ^ 2) hc hc2' ?_ ?_
      · rwa [Units.val_pow_eq_pow_val]
      ·
        rwa [Units.val_pow_eq_pow_val, ← pow_succ']
    rw [tateToricPoint_fst_eq, tateToricPoint_fst_eq, show ((0 : ℤ)) = ((0 : ℕ) : ℤ) from rfl,
      HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff] at hu
    exact (hu.map (IsLocalRing.residue A)).ne_zero hcoef
  · rw [map_sub, map_sub, map_toricX _ N c hc, map_toricX _ N (c ^ 2) hc2', ← tateToricPoint_fst_eq, ← tateToricPoint_fst_eq,
      map_pow]


-- created on 2026-10-23
