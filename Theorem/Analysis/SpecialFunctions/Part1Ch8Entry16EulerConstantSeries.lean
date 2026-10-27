/-
Author: @akiezun, Avocado
-/

import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.NormNum.Parity
import Def.Analysis.SpecialFunctions.Part1Ch8Entry16EulerConstantSeries
/-!
# Ramanujan's Notebooks, Part I, Chapter 8

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace Ramanujan.Part1Ch8

namespace Entry16Eulerconstantseries

open scoped BigOperators Real

open Topology

noncomputable section

theorem one_le_pow3 (k : ℕ) : 1 ≤ 3 ^ k := Nat.one_le_pow k 3 (by norm_num)

theorem two_dvd_pow3_sub_one (k : ℕ) : 2 ∣ (3 ^ k - 1) := by
  have hodd : Odd (3 ^ k) := Odd.pow (by norm_num)
  obtain ⟨m, hm⟩ := hodd
  have h1 : 1 ≤ 3 ^ k := one_le_pow3 k
  omega

theorem two_mul_A_add_one (k : ℕ) : 2 * ((3 ^ k - 1) / 2) + 1 = 3 ^ k := by
  have h1 : 1 ≤ 3 ^ k := one_le_pow3 k
  have hdvd := two_dvd_pow3_sub_one k
  obtain ⟨t, ht⟩ := hdvd
  omega

theorem A_succ (k : ℕ) : Afun (k + 1) = 3 * Afun k + 1 := by
  have h1 := two_mul_A_add_one k
  have h2 := two_mul_A_add_one (k + 1)
  have h3 : 3 ^ (k + 1) = 3 ^ k * 3 := pow_succ 3 k
  unfold Afun
  omega

theorem Hsum_zero : Hsum 0 = 0 := by simp [Hsum]

theorem Hsum_succ (n : ℕ) : Hsum (n + 1) = Hsum n + (((n + 1 : ℕ) : ℝ))⁻¹ := by
  unfold Hsum
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]

theorem partial_frac (x : ℝ) (hx0 : x ≠ 0) (hx1 : x - 1 ≠ 0) (hx2 : x + 1 ≠ 0) :
    (1 : ℝ) / (x ^ 3 - x) = -1 / x + 1 / (2 * (x - 1)) + 1 / (2 * (x + 1)) := by
  have hx3 : x ^ 3 - x ≠ 0 := by
    have : x ^ 3 - x = x * (x - 1) * (x + 1) := by ring
    rw [this]
    exact mul_ne_zero (mul_ne_zero hx0 hx1) hx2
  have hx4 : x ^ 2 - 1 ≠ 0 := by
    have : x ^ 2 - 1 = (x - 1) * (x + 1) := by ring
    rw [this]
    exact mul_ne_zero hx1 hx2
  field_simp
  ring

theorem gfun_step (M : ℕ) :
    gfun (M + 1) =
      (((((3 * M + 2 : ℕ) : ℝ))⁻¹ + (((3 * M + 3 : ℕ) : ℝ))⁻¹ + (((3 * M + 4 : ℕ) : ℝ))⁻¹) -
        (((M + 1 : ℕ) : ℝ))⁻¹) / 2 := by
  have hcast1 : (1 : ℝ) ≤ (((M + 1 : ℕ) : ℝ)) := by
    have h : 1 ≤ M + 1 := Nat.succ_le_succ (Nat.zero_le M)
    exact_mod_cast h
  have hmR : (((M + 1 : ℕ) : ℝ)) ≠ 0 := by
    have hpos : (0 : ℝ) < (((M + 1 : ℕ) : ℝ)) := by linarith
    exact ne_of_gt hpos
  have hu0 : (3 : ℝ) * (((M + 1 : ℕ) : ℝ)) ≠ 0 := mul_ne_zero (by norm_num) hmR
  have hu1 : (3 : ℝ) * (((M + 1 : ℕ) : ℝ)) - 1 ≠ 0 := by
    have h3m : (3 : ℝ) * (((M + 1 : ℕ) : ℝ)) ≥ 3 := by nlinarith
    linarith
  have hu2 : (3 : ℝ) * (((M + 1 : ℕ) : ℝ)) + 1 ≠ 0 := by positivity
  have hpf := partial_frac ((3 : ℝ) * (((M + 1 : ℕ) : ℝ))) hu0 hu1 hu2
  have e1 : (3 : ℝ) * (((M + 1 : ℕ) : ℝ)) - 1 = (((3 * M + 2 : ℕ) : ℝ)) := by
    push_cast
    ring
  have e2 : (3 : ℝ) * (((M + 1 : ℕ) : ℝ)) = (((3 * M + 3 : ℕ) : ℝ)) := by
    push_cast
    ring
  have e3 : (3 : ℝ) * (((M + 1 : ℕ) : ℝ)) + 1 = (((3 * M + 4 : ℕ) : ℝ)) := by
    push_cast
    ring
  unfold gfun
  rw [hpf, e3, e1, ← e2]
  field_simp
  ring

theorem G_formula (M : ℕ) :
    ∑ j ∈ Finset.Icc 1 M, gfun j = (Hsum (3 * M + 1) - Hsum M - 1) / 2 := by
  induction M with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add]
    rw [Finset.Icc_eq_empty (by norm_num : ¬ (1 : ℕ) ≤ 0)]
    simp only [Finset.sum_empty]
    have h1 : Hsum 1 = 1 := by
      have h := Hsum_succ 0
      simp [Hsum_zero] at h
      linarith [h]
    rw [Hsum_zero, h1]
    norm_num
  | succ M ih =>
    have hsum_g : ∑ j ∈ Finset.Icc 1 (M + 1), gfun j =
        (∑ j ∈ Finset.Icc 1 M, gfun j) + gfun (M + 1) := by
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ M + 1)]
    have hH1 : Hsum (3 * M + 2) = Hsum (3 * M + 1) + (((3 * M + 2 : ℕ) : ℝ))⁻¹ := by
      have h : 3 * M + 2 = (3 * M + 1) + 1 := by omega
      rw [h]
      exact Hsum_succ (3 * M + 1)
    have hH2 : Hsum (3 * M + 3) = Hsum (3 * M + 2) + (((3 * M + 3 : ℕ) : ℝ))⁻¹ := by
      have h : 3 * M + 3 = (3 * M + 2) + 1 := by omega
      rw [h]
      exact Hsum_succ (3 * M + 2)
    have hH3 : Hsum (3 * M + 4) = Hsum (3 * M + 3) + (((3 * M + 4 : ℕ) : ℝ))⁻¹ := by
      have h : 3 * M + 4 = (3 * M + 3) + 1 := by omega
      rw [h]
      exact Hsum_succ (3 * M + 3)
    have hHM : Hsum (M + 1) = Hsum M + (((M + 1 : ℕ) : ℝ))⁻¹ := Hsum_succ M
    have h3M : 3 * (M + 1) + 1 = 3 * M + 4 := by omega
    rw [hsum_g, ih, gfun_step, h3M, hH3, hH2, hH1, hHM]
    ring

theorem block_sum_id (f : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b) :
    ∑ j ∈ Finset.Icc (a + 1) b, f j =
      (∑ j ∈ Finset.Icc 1 b, f j) - (∑ j ∈ Finset.Icc 1 a, f j) := by
  have hunion : Finset.Icc 1 a ∪ Finset.Icc (a + 1) b = Finset.Icc 1 b := by
    ext x
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  have hdisj : Disjoint (Finset.Icc 1 a) (Finset.Icc (a + 1) b) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_Icc] at hx1 hx2
    omega
  have hsum := Finset.sum_union hdisj (f := f)
  rw [hunion] at hsum
  linarith [hsum]

theorem block_eq (k : ℕ) :
    ∑ j ∈ Finset.Icc (Afun k + 1) (Afun (k + 1)), gfun j =
      ((Hsum (Afun (k + 2)) - Hsum (Afun (k + 1)) - 1) / 2) -
      ((Hsum (Afun (k + 1)) - Hsum (Afun k) - 1) / 2) := by
  have hmono : Afun k ≤ Afun (k + 1) := by
    have h := A_succ k
    unfold Afun at h ⊢
    omega
  have h1 : 3 * Afun k + 1 = Afun (k + 1) := (A_succ k).symm
  have h2 : 3 * Afun (k + 1) + 1 = Afun (k + 2) := (A_succ (k + 1)).symm
  have b1 := block_sum_id gfun (Afun k) (Afun (k + 1)) hmono
  rw [G_formula (Afun (k + 1)), G_formula (Afun k), h1, h2] at b1
  exact b1

theorem gfun_nonneg (j : ℕ) (hj : 1 ≤ j) : 0 ≤ gfun j := by
  unfold gfun
  apply le_of_lt
  apply one_div_pos.mpr
  have hjr : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have h1 : (0 : ℝ) < (j : ℝ) := by linarith
  have h2 : (1 : ℝ) < (3 * (j : ℝ)) ^ 2 := by nlinarith [hjr]
  have hD : (3 * (j : ℝ)) ^ 3 - 3 * (j : ℝ) = 3 * (j : ℝ) * (((3 * (j : ℝ)) ^ 2) - 1) := by ring
  rw [hD]
  apply mul_pos (by linarith)
  linarith

theorem gfun_le_inv_cube (j : ℕ) (hj : 1 ≤ j) :
    gfun j ≤ 1 / (24 * ((j : ℝ)) ^ 3) := by
  unfold gfun
  have hjr : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hjpos : (0 : ℝ) < (j : ℝ) := by linarith
  have h24pos : (0 : ℝ) < 24 * ((j : ℝ)) ^ 3 := by positivity
  apply one_div_le_one_div_of_le h24pos
  have hD : (3 * (j : ℝ)) ^ 3 - 3 * (j : ℝ) - 24 * ((j : ℝ)) ^ 3 =
      3 * ((j : ℝ)) * (((j : ℝ)) ^ 2 - 1) := by ring
  have hsq : (1 : ℝ) ≤ ((j : ℝ)) ^ 2 := by nlinarith [hjr]
  have hnn : (0 : ℝ) ≤ 3 * ((j : ℝ)) * (((j : ℝ)) ^ 2 - 1) := by
    apply mul_nonneg
    · apply mul_nonneg (by norm_num)
      exact le_of_lt hjpos
    · linarith
  linarith [hD, hnn]

theorem A_cast (k : ℕ) : ((Afun k : ℝ)) = ((((3 ^ k : ℕ) : ℝ)) - 1) / 2 := by
  have hdvd : 2 ∣ (3 ^ k - 1) := two_dvd_pow3_sub_one k
  have h1 : (1 : ℕ) ≤ 3 ^ k := one_le_pow3 k
  have hcast : ((((3 ^ k - 1) : ℕ) : ℝ)) = ((((3 ^ k : ℕ) : ℝ))) - 1 := by
    rw [Nat.cast_sub h1, Nat.cast_one]
  have hA : Afun k = (3 ^ k - 1) / 2 := rfl
  have h2 : ((Afun k : ℝ)) = ((((3 ^ k - 1 : ℕ) : ℝ))) / ((((2 : ℕ) : ℝ))) := by
    rw [hA]
    exact Nat.cast_div hdvd (by norm_num)
  rw [h2, hcast]
  norm_num

theorem block_card (k : ℕ) :
    (Finset.Icc (Afun k + 1) (Afun (k + 1))).card = 3 ^ k := by
  have h1 := two_mul_A_add_one k
  have h2 := two_mul_A_add_one (k + 1)
  have h3 : 3 ^ (k + 1) = 3 ^ k * 3 := pow_succ 3 k
  have hA1 : Afun k = (3 ^ k - 1) / 2 := rfl
  have hA2 : Afun (k + 1) = (3 ^ (k + 1) - 1) / 2 := rfl
  rw [hA1, hA2, Nat.card_Icc]
  omega

theorem block_sum_le (k : ℕ) :
    ∑ j ∈ Finset.Icc (Afun k + 1) (Afun (k + 1)), gfun j ≤
      (((1 / 9 : ℝ)) ^ k) / 3 := by
  have hAlo : ((Afun k : ℝ)) = ((((3 ^ k : ℕ) : ℝ)) - 1) / 2 := A_cast k
  have h3k : (0 : ℝ) < (((3 ^ k : ℕ) : ℝ)) := by
    have hpos : 0 < 3 ^ k := Nat.pow_pos (by norm_num)
    exact_mod_cast hpos
  have hTne : ((((3 ^ k : ℕ) : ℝ))) ≠ 0 := ne_of_gt h3k
  have h3kR : ((((3 ^ k : ℕ) : ℝ))) = (3 : ℝ) ^ k := by push_cast; ring
  have h9t : (((1 / 9 : ℝ)) ^ k) = 1 / (((((3 ^ k : ℕ) : ℝ))) * ((((3 ^ k : ℕ) : ℝ)))) := by
    rw [div_pow, one_pow]
    congr 1
    rw [h3kR]
    have h9 : (9 : ℝ) = (3 : ℝ) ^ 2 := by norm_num
    rw [h9, ← pow_mul]
    have h2k : 2 * k = k + k := by ring
    rw [h2k, pow_add]
  have hjbound : ∀ j ∈ Finset.Icc (Afun k + 1) (Afun (k + 1)),
      gfun j ≤ (((((1 / 9 : ℝ)) ^ k) / 3)) / ((((3 ^ k : ℕ) : ℝ))) := by
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have hj1 : 1 ≤ j := by
      have hA0 : 0 ≤ Afun k := Nat.zero_le _
      omega
    have hle : ((Afun k + 1 : ℕ) : ℝ) ≤ ((j : ℝ)) := by exact_mod_cast hj.1
    have hAle : (((((3 ^ k : ℕ) : ℝ)) + 1) / 2) ≤ ((j : ℝ)) := by
      have hcast1 : ((Afun k + 1 : ℕ) : ℝ) = ((Afun k : ℝ)) + 1 := by
        push_cast; ring
      rw [hcast1, hAlo] at hle
      linarith [hle]
    have hle2 : (((((3 ^ k : ℕ) : ℝ))) / 2) ≤ ((j : ℝ)) := by linarith [hAle]
    have hcube : (((((3 ^ k : ℕ) : ℝ))) / 2) ^ 3 ≤ ((j : ℝ)) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hle2 3
    have hstep := gfun_le_inv_cube j hj1
    have hden : (3 : ℝ) * (((((3 ^ k : ℕ) : ℝ))) * ((((3 ^ k : ℕ) : ℝ)))) * ((((3 ^ k : ℕ) : ℝ))) ≤
        24 * ((j : ℝ)) ^ 3 := by
      nlinarith [hcube, h3k]
    have hC : (((((1 / 9 : ℝ)) ^ k) / 3)) / ((((3 ^ k : ℕ) : ℝ))) =
        1 / (3 * (((((3 ^ k : ℕ) : ℝ))) * ((((3 ^ k : ℕ) : ℝ)))) * ((((3 ^ k : ℕ) : ℝ)))) := by
      rw [h9t]
      field_simp
    have hjr : (1 : ℝ) ≤ ((j : ℝ)) := by exact_mod_cast hj1
    have hjpos : (0 : ℝ) < ((j : ℝ)) := by linarith
    have hDge : (24 : ℝ) * ((j : ℝ)) ^ 3 ≤ (3 * ((j : ℝ))) ^ 3 - 3 * ((j : ℝ)) := by
      have hD : (3 * (j : ℝ)) ^ 3 - 3 * ((j : ℝ)) - 24 * ((j : ℝ)) ^ 3 =
          3 * ((j : ℝ)) * (((j : ℝ)) ^ 2 - 1) := by ring
      have hsq : (1 : ℝ) ≤ ((j : ℝ)) ^ 2 := by nlinarith [hjr]
      have hnn : (0 : ℝ) ≤ 3 * ((j : ℝ)) * (((j : ℝ)) ^ 2 - 1) := by
        apply mul_nonneg
        · apply mul_nonneg (by norm_num)
          exact le_of_lt hjpos
        · linarith
      linarith [hD, hnn]
    rw [hC]
    apply one_div_le_one_div_of_le (by positivity)
    linarith [hden, hDge]
  have hle := Finset.sum_le_card_nsmul _ _ _ hjbound
  rw [block_card, nsmul_eq_mul] at hle
  have hcancel : ((((3 ^ k : ℕ) : ℝ))) * (((((1 / 9 : ℝ)) ^ k) / 3) / ((((3 ^ k : ℕ) : ℝ)))) =
      ((((1 / 9 : ℝ)) ^ k) / 3) := by
    rw [← mul_div_assoc]
    exact mul_div_cancel_left₀ _ hTne
  rwa [hcancel] at hle

theorem majorant_summable :
    Summable (fun n : ℕ => ((((n : ℝ)) + 1) * (1 / 9 : ℝ) ^ n) / 3) := by
  have hnorm : ‖(1 / 9 : ℝ)‖ < 1 := by norm_num
  have hpow : Summable (fun n : ℕ => ((n : ℝ)) ^ 1 * (1 / 9 : ℝ) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 1 hnorm
  have hpow' : Summable (fun n : ℕ => ((n : ℝ)) * (1 / 9 : ℝ) ^ n) := by
    simpa [pow_one] using hpow
  have hgeo : Summable (fun n : ℕ => (1 / 9 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hadd : Summable (fun n : ℕ => (((n : ℝ)) * (1 / 9 : ℝ) ^ n + (1 / 9 : ℝ) ^ n)) :=
    hpow'.add hgeo
  have hmr := hadd.mul_right (1 / 3 : ℝ)
  have heq : (fun n : ℕ => ((((n : ℝ)) + 1) * (1 / 9 : ℝ) ^ n) / 3) =
      (fun n : ℕ => ((((n : ℝ)) * (1 / 9 : ℝ) ^ n + (1 / 9 : ℝ) ^ n)) * (1 / 3)) := by
    funext n
    ring
  rwa [heq]

theorem Tfun_eq (k : ℕ) : Tfun k =
    ((k + 1 : ℕ) : ℝ) * ∑ j ∈ Finset.Icc (Afun k + 1) (Afun (k + 1)), gfun j := by
  unfold Tfun gfun
  rfl

theorem Tfun_nonneg (k : ℕ) : 0 ≤ Tfun k := by
  rw [Tfun_eq]
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro j hj
  simp only [Finset.mem_Icc] at hj
  have hA0 : 0 ≤ Afun k := Nat.zero_le _
  have hj1 : 1 ≤ j := by omega
  exact gfun_nonneg j hj1

theorem Tfun_le (k : ℕ) :
    Tfun k ≤ ((((k : ℝ)) + 1) * (1 / 9 : ℝ) ^ k) / 3 := by
  rw [Tfun_eq]
  have hblk := block_sum_le k
  have hcast : (((k + 1 : ℕ) : ℝ)) = ((k : ℝ)) + 1 := by push_cast; ring
  rw [hcast]
  calc (((k : ℝ)) + 1) * ∑ j ∈ Finset.Icc (Afun k + 1) (Afun (k + 1)), gfun j
      ≤ (((k : ℝ)) + 1) * ((((1 / 9 : ℝ)) ^ k) / 3) := by
        apply mul_le_mul_of_nonneg_left hblk (by positivity)
    _ = ((((k : ℝ)) + 1) * (1 / 9 : ℝ) ^ k) / 3 := by ring

theorem summable_tfun : Summable Tfun :=
  Summable.of_nonneg_of_le Tfun_nonneg Tfun_le majorant_summable

theorem Hsum_cast : ∀ n : ℕ, ((((harmonic n : ℚ)) : ℝ)) = Hsum n := by
  intro n
  rw [harmonic_eq_sum_Icc]
  unfold Hsum
  push_cast
  rfl

theorem H_rate (n : ℕ) (hn : 1 ≤ n) :
    |((Hsum n - Real.log ((n : ℝ))) - Real.eulerMascheroniConstant)| ≤ 1 / ((n : ℝ)) := by
  have hn0 : n ≠ 0 := by omega
  have hnpos : (0 : ℝ) < ((n : ℝ)) := by exact_mod_cast hn
  have hcast := Hsum_cast n
  have hseq : Real.eulerMascheroniSeq n = Hsum n - Real.log (((n : ℝ)) + 1) := by
    unfold Real.eulerMascheroniSeq
    rw [hcast]
  have hseq' : Real.eulerMascheroniSeq' n = Hsum n - Real.log ((n : ℝ)) := by
    unfold Real.eulerMascheroniSeq'
    rw [ite_eq_right hn0, hcast]
  have h1 := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant n
  have h2 := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' n
  rw [hseq] at h1
  rw [hseq'] at h2
  have hlog : Real.log (((n : ℝ)) + 1) - Real.log ((n : ℝ)) ≤ 1 / ((n : ℝ)) := by
    have hdiv : Real.log (((n : ℝ)) + 1) - Real.log ((n : ℝ)) =
        Real.log (1 + 1 / ((n : ℝ))) := by
      rw [← Real.log_div (by positivity) (ne_of_gt hnpos)]
      congr 1
      field_simp
    rw [hdiv]
    have hle := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + 1 / ((n : ℝ)))
    have heq : (1 + 1 / ((n : ℝ))) - 1 = 1 / ((n : ℝ)) := by ring
    rwa [heq] at hle
  rw [abs_le]
  constructor <;> linarith [h1, h2, hlog, hnpos]

theorem key_decay :
    Filter.Tendsto (fun N : ℕ => (((N : ℝ)) + 1) * (1 / 3 : ℝ) ^ N) Filter.atTop (nhds 0) := by
  have hnorm : ‖(1 / 3 : ℝ)‖ < 1 := by norm_num
  have hpow : Summable (fun n : ℕ => ((n : ℝ)) ^ 1 * (1 / 3 : ℝ) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 1 hnorm
  have hpow' : Summable (fun n : ℕ => ((n : ℝ)) * (1 / 3 : ℝ) ^ n) := by
    simpa [pow_one] using hpow
  have hgeo : Summable (fun n : ℕ => (1 / 3 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hadd : Summable (fun n : ℕ => (((n : ℝ)) * (1 / 3 : ℝ) ^ n + (1 / 3 : ℝ) ^ n)) :=
    hpow'.add hgeo
  have hsum : Summable (fun n : ℕ => ((((n : ℝ)) + 1) * (1 / 3 : ℝ) ^ n)) := by
    have heq : (fun n : ℕ => ((((n : ℝ)) + 1) * (1 / 3 : ℝ) ^ n)) =
        (fun n : ℕ => ((((n : ℝ)) * (1 / 3 : ℝ) ^ n + (1 / 3 : ℝ) ^ n))) := by
      funext n
      rw [add_mul, one_mul]
    rwa [heq]
  exact hsum.tendsto_atTop_zero

theorem geo_third :
    Filter.Tendsto (fun N : ℕ => (1 / 3 : ℝ) ^ N) Filter.atTop (nhds 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

end
end Entry16Eulerconstantseries
end Ramanujan.Part1Ch8
end
