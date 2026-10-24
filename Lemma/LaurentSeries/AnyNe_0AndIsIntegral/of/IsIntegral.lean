import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_ModularCurve_X0
import Lemma.Definitions.Def_ModularCurve_LaurentCoeff
import Lemma.Int.P2MUtil


/--
[ModularCurve_exists_int_ne_zero_isIntegral_adjoin_int_of_isIntegral_adjoin_rat](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_exists_int_ne_zero_isIntegral_adjoin_int_of_isIntegral_adjoin_rat.lean)
-/

private lemma  adjoinRat_exists_int_mul_mem_adjoinInt (t : LaurentSeries ℚ) {y : LaurentSeries ℚ}
  (hy : y ∈ Algebra.adjoin ℚ ({t} : Set (LaurentSeries ℚ))) :
  ∃ D : ℤ, D ≠ 0 ∧ (D : LaurentSeries ℚ) * y ∈ Algebra.adjoin ℤ ({t} : Set (LaurentSeries ℚ)) := by
  induction hy using Algebra.adjoin_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using Algebra.subset_adjoin hx⟩
  | algebraMap r =>
      refine ⟨r.den, by exact_mod_cast r.den_ne_zero, ?_⟩
      have h : ((r.den : ℤ) : LaurentSeries ℚ) * algebraMap ℚ (LaurentSeries ℚ) r = (r.num : LaurentSeries ℚ) := by
        rw [Int.cast_natCast, ← map_natCast (algebraMap ℚ (LaurentSeries ℚ)), ← map_mul,
          Rat.den_mul_eq_num, map_intCast]
      rw [h]
      exact intCast_mem _ _
  | add x y _ _ hx hy =>
      obtain ⟨D₁, h₁, m₁⟩ := hx
      obtain ⟨D₂, h₂, m₂⟩ := hy
      refine ⟨D₁ * D₂, mul_ne_zero h₁ h₂, ?_⟩
      have h : ((D₁ * D₂ : ℤ) : LaurentSeries ℚ) * (x + y) = (D₂ : LaurentSeries ℚ) * ((D₁ : LaurentSeries ℚ) * x)
        + (D₁ : LaurentSeries ℚ) * ((D₂ : LaurentSeries ℚ) * y) := by
        push_cast; ring
      rw [h]
      exact add_mem (mul_mem (intCast_mem _ _) m₁) (mul_mem (intCast_mem _ _) m₂)
  | mul x y _ _ hx hy =>
      obtain ⟨D₁, h₁, m₁⟩ := hx
      obtain ⟨D₂, h₂, m₂⟩ := hy
      refine ⟨D₁ * D₂, mul_ne_zero h₁ h₂, ?_⟩
      have h : ((D₁ * D₂ : ℤ) : LaurentSeries ℚ) * (x * y) = ((D₁ : LaurentSeries ℚ) * x) * ((D₂ : LaurentSeries ℚ) * y) := by
        push_cast; ring
      rw [h]
      exact mul_mem m₁ m₂

open Polynomial in
@[path]
private lemma main
  {t x : LaurentSeries ℚ}
-- given
  (hx : IsIntegral (Algebra.adjoin ℚ ({t} : Set (LaurentSeries ℚ))) x) :
-- imply
  ∃ d : ℤ, d ≠ 0 ∧
      IsIntegral (Algebra.adjoin ℤ ({t} : Set (LaurentSeries ℚ)))
        (algebraMap ℚ (LaurentSeries ℚ) (d : ℚ) * x) := by
  classical
  obtain ⟨p, hpm, hp0⟩ := hx
  set q : (LaurentSeries ℚ)[X] := p.map (algebraMap _ (LaurentSeries ℚ)) with hq
  have hqm : q.Monic := hpm.map _
  have hq0 : q.eval x = 0 := by rw [hq, eval_map]; exact hp0
  have hcoef : ∀ i, q.coeff i ∈ Algebra.adjoin ℚ ({t} : Set (LaurentSeries ℚ)) := fun i => by rw [hq, coeff_map]; exact (p.coeff i).2
  choose D hD0 hDmem using fun i => adjoinRat_exists_int_mul_mem_adjoinInt t (hcoef i)
  set N := q.natDegree with hN
  refine ⟨∏ i ∈ Finset.range N, D i, Finset.prod_ne_zero_iff.mpr fun i _ => hD0 i, ?_⟩
  rw [map_intCast]
  set Dall : ℤ := ∏ i ∈ Finset.range N, D i with hDall
  have hDallmem : ∀ i, i < N → (Dall : LaurentSeries ℚ) * q.coeff i ∈ Algebra.adjoin ℤ ({t} : Set (LaurentSeries ℚ)) := by
-- proof
    intro i hi
    have hi' : i ∈ Finset.range N := Finset.mem_range.mpr hi
    rw [hDall, ← Finset.prod_erase_mul _ _ hi', Int.cast_mul, Int.cast_prod, mul_assoc]
    exact mul_mem (prod_mem fun j _ => intCast_mem _ _) (hDmem i)
  set r : (LaurentSeries ℚ)[X] := q.scaleRoots (Dall : LaurentSeries ℚ) with hr
  have hrm : r.Monic := (monic_scaleRoots_iff _).mpr hqm
  have hr0 : r.eval ((Dall : LaurentSeries ℚ) * x) = 0 := by
    have := scaleRoots_eval₂_eq_zero (RingHom.id (LaurentSeries ℚ)) (r := x) (s := (Dall : LaurentSeries ℚ))
      (by simpa [eval₂_id] using hq0)
    simpa [eval₂_id] using this
  have hrcoef : ∀ i, r.coeff i ∈ Algebra.adjoin ℤ ({t} : Set (LaurentSeries ℚ)) := by
    intro i
    rw [hr, coeff_scaleRoots]
    rcases lt_trichotomy i N with hi | rfl | hi
    ·
      obtain ⟨k, hk⟩ : ∃ k, N - i = k + 1 := ⟨N - i - 1, by omega⟩
      rw [hk, pow_succ', ← mul_assoc, mul_comm (q.coeff i)]
      exact mul_mem (hDallmem i hi) (pow_mem (intCast_mem _ _) _)
    ·
      rw [Nat.sub_self, pow_zero, mul_one]
      simp [hN, hqm.coeff_natDegree]
    ·
      rw [coeff_eq_zero_of_natDegree_lt hi, zero_mul]
      exact zero_mem _
  have hlifts : r ∈ lifts (algebraMap (Algebra.adjoin ℤ ({t} : Set (LaurentSeries ℚ))) (LaurentSeries ℚ)) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    exact ⟨⟨r.coeff i, hrcoef i⟩, rfl⟩
  obtain ⟨r', hr'map, -, hr'm⟩ := lifts_and_degree_eq_and_monic hlifts hrm
  exact ⟨r', hr'm, by rw [← eval_map, hr'map, hr0]⟩


-- created on 2026-10-23
