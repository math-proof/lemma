import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.EllipticCurve_RubinSilverbergFamily
import Lemma.Int.P2MUtil
open Polynomial
open RubinSilverberg


/-- ported from external source -/

private lemma  map_kleinH
  {R : Type*}
  [CommRing R]
  {S : Type*} [CommRing S] (f : R →+* S) (u : R) : f (kleinH u) = kleinH (f u) := by
  simp [kleinH, map_ofNat]

private lemma  map_kleinV
  {R : Type*}
  [CommRing R]
  {S : Type*} [CommRing S] (f : R →+* S) (u : R) : f (kleinV u) = kleinV (f u) := by
  simp [kleinV, map_ofNat]

private lemma  map_kleinT
  {R : Type*}
  [CommRing R]
  {S : Type*} [CommRing S] (f : R →+* S) (u : R) : f (kleinT u) = kleinT (f u) := by
  simp [kleinT, map_ofNat]

private lemma  bezout_kleinH_kleinV_s10
  {R : Type*}
  [CommRing R]
  (u : R) :
  (3125 - 33022 * u ^ 5 - 3003 * u ^ 10) * kleinH u +
    (679478 * u ^ 4 + 1485989 * u ^ 9 - 684695 * u ^ 14 + 3003 * u ^ 19) * kleinV u = 3125 := by
  unfold kleinH kleinV
  ring

private lemma  bezout_kleinH_kleinT_s10
  {R : Type*}
  [CommRing R]
  (u : R) :
  (950431323 + 20237705983 * u ^ 5 - 103588896 * u ^ 10 + 20237108822 * u ^ 15
      - 1055557719 * u ^ 20 - 2022161 * u ^ 25) * kleinH u +
    (455818677 + 1001301767 * u ^ 5 - 461063031 * u ^ 10 + 2022161 * u ^ 15) * kleinT u =
    1406250000 := by
  unfold kleinH kleinT
  ring

private lemma  kleinT_sq_sub_kleinH_cube'
  {R : Type*}
  [CommRing R]
  (u : R) : kleinT u ^ 2 - kleinH u ^ 3 = 1728 * kleinV u ^ 5 := by
  unfold kleinT kleinH kleinV
  ring

private lemma  natDegree_kleinH_X_le
  {R : Type*}
  [CommRing R]
  [Nontrivial R] : (kleinH (X : R[X])).natDegree ≤ 20 := by
  unfold kleinH
  compute_degree

private lemma  coeff_kleinH_X
  {R : Type*}
  [CommRing R]
  [Nontrivial R] : (kleinH (X : R[X])).coeff 20 = 1 := by
  unfold kleinH
  simp [coeff_X_pow, coeff_one, ← C_ofNat, coeff_C_mul]

private lemma  natDegree_kleinV_X_le
  {R : Type*}
  [CommRing R]
  [Nontrivial R] : (kleinV (X : R[X])).natDegree ≤ 11 := by
  unfold kleinV
  compute_degree

private lemma  IsKleinDatum.kleinH_ne_zero_s10
  {K : Type*}
  [Field K]
  [CharZero K] {a b u₀ : K} (h : IsKleinDatum a b u₀) (ha : a ≠ 0) :
  kleinH u₀ ≠ 0 := by
  intro hH
  obtain ⟨heq, hV⟩ := h
  rw [hH, zero_pow three_ne_zero, zero_mul, zero_add] at heq
  have : (6912 : K) ≠ 0 := by norm_num
  exact hV (eq_zero_of_pow_eq_zero (eq_zero_of_ne_zero_of_mul_left_eq_zero (mul_ne_zero this (pow_ne_zero 3 ha)) heq))

private lemma  IsKleinDatum.disc_ne_zero_s10
  {K : Type*}
  [Field K]
  [CharZero K] {a b u₀ : K} (h : IsKleinDatum a b u₀) (ha : a ≠ 0) :
  4 * a ^ 3 + 27 * b ^ 2 ≠ 0 := by
  intro hD
  obtain ⟨heq, hV⟩ := h
  rw [hD, mul_zero, zero_add] at heq
  have : (6912 : K) ≠ 0 := by norm_num
  exact hV (eq_zero_of_pow_eq_zero (eq_zero_of_ne_zero_of_mul_left_eq_zero (mul_ne_zero this (pow_ne_zero 3 ha)) heq))

private lemma _root_.RubinSilverberg.IsKleinDatum.kleinT_sq_mul
  {K : Type*}
  [Field K]
  {a b u₀ : K} (h : IsKleinDatum a b u₀) :
  kleinT u₀ ^ 2 * (4 * a ^ 3 + 27 * b ^ 2) = 46656 * b ^ 2 * kleinV u₀ ^ 5 := by
  have hs := kleinT_sq_sub_kleinH_cube' u₀
  linear_combination (4 * a ^ 3 + 27 * b ^ 2) * hs + h.1
p2m_export "RubinSilverberg" "IsKleinDatum.kleinT_sq_mul"

private lemma _root_.RubinSilverberg.IsKleinDatum.kleinT_ne_zero_s10
  {K : Type*}
  [Field K]
  [CharZero K] {a b u₀ : K} (h : IsKleinDatum a b u₀) (hb : b ≠ 0) :
  kleinT u₀ ≠ 0 := by
  intro hT
  have heq := h.kleinT_sq_mul
  rw [hT, zero_pow two_ne_zero, zero_mul] at heq
  have : (46656 : K) ≠ 0 := by norm_num
  exact h.2 (eq_zero_of_pow_eq_zero
    (eq_zero_of_ne_zero_of_mul_left_eq_zero (mul_ne_zero this (pow_ne_zero 2 hb)) heq.symm))
p2m_export "RubinSilverberg" "IsKleinDatum.kleinT_ne_zero_s10"

private lemma  exists_isKleinDatum_s10
  {K : Type*}
  [Field K]
  [IsAlgClosed K] [CharZero K] (a b : K)
  (hD : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) : ∃ u₀ : K, IsKleinDatum a b u₀ := by
  set P : K[X] := C (4 * a ^ 3 + 27 * b ^ 2) * kleinH X ^ 3 + C (6912 * a ^ 3) * kleinV X ^ 5 with hP
  have hcoeff : P.coeff 60 = 4 * a ^ 3 + 27 * b ^ 2 := by
    have h1 : (kleinH (X : K[X]) ^ 3).coeff 60 = 1 := by
      have := coeff_pow_of_natDegree_le (natDegree_kleinH_X_le (R := K)) (m := 3)
      rwa [show 3 * 20 = 60 from rfl, coeff_kleinH_X, one_pow] at this
    have h2 : (kleinV (X : K[X]) ^ 5).coeff 60 = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      calc
        _ ≤ 5 * (kleinV (X : K[X])).natDegree := natDegree_pow_le
        _ ≤ 5 * 11 := Nat.mul_le_mul_left 5 natDegree_kleinV_X_le
        _ < 60 := by norm_num
    rw [hP, coeff_add, coeff_C_mul, coeff_C_mul, h1, h2, mul_one, mul_zero, add_zero]
  have hdeg : P.degree ≠ 0 := by
    intro h0
    have h60 : 60 ≤ P.natDegree := le_natDegree_of_ne_zero (by rw [hcoeff]; apply hD)
    have := natDegree_eq_zero_iff_degree_le_zero.mpr h0.le
    omega
  obtain ⟨u₀, hu₀⟩ := IsAlgClosed.exists_root P hdeg
  have heval : kleinH u₀ ^ 3 * (4 * a ^ 3 + 27 * b ^ 2) + 6912 * a ^ 3 * kleinV u₀ ^ 5 = 0 := by
    have h := hu₀
    rw [IsRoot.def, hP, eval_add, eval_mul, eval_mul, eval_C, eval_C, eval_pow, eval_pow,
      ← coe_evalRingHom, map_kleinH, map_kleinV, coe_evalRingHom, eval_X] at h
    linear_combination h
  refine ⟨u₀, heval, fun hV ↦ ?_⟩
  have hH : kleinH u₀ = 0 := by
    rw [hV, zero_pow (by norm_num), mul_zero, add_zero] at heval
    exact eq_zero_of_pow_eq_zero (eq_zero_of_ne_zero_of_mul_right_eq_zero hD heval)
  have hbez := bezout_kleinH_kleinV_s10 u₀
  rw [hH, hV, mul_zero, mul_zero, add_zero] at hbez
  norm_num at hbez
p2m_open "RubinSilverberg P2MW.S_RubinSilverberg_IsKleinDatum_kleinT_ne_zero.RubinSilverberg"
@[path]
private lemma main
  [Field K] [CharZero K]
  {a b u₀ : K}
-- given
  (h : RubinSilverberg.IsKleinDatum a b u₀)
  (hb : b ≠ 0) :
-- imply
  RubinSilverberg.kleinT u₀ ≠ 0 :=
-- proof
  h.kleinT_ne_zero_s10 hb


-- created on 2026-10-23
