import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry9IiGeneralizedbellgeneratingDefining
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Entry9IiGeneralizedbellgeneratingDefining


namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry9IiGeneralizedbellgeneratingDefining

/--
[summable_bellTerm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry9IiGeneralizedbellgeneratingDefining.lean)
-/
@[path]
private lemma summable_bellTerm (a b x : ℂ) (n : ℕ) :
  Summable (fun k : ℕ => (a + b * (↑(k + 1) : ℂ)) ^ n * x ^ (k + 1) / (↑(Nat.factorial k) : ℂ)) := by
  have hYsum : Summable (fun k : ℕ => (2 ^ n * ‖x‖) ^ k / (Nat.factorial k : ℝ)) :=
    Real.summable_pow_div_factorial (2 ^ n * ‖x‖)
  have hCsum : Summable (fun k : ℕ => (‖a‖ + ‖b‖) ^ n * 2 ^ n * ‖x‖ *
    ((2 ^ n * ‖x‖) ^ k / (Nat.factorial k : ℝ))) :=
    hYsum.mul_left _
  refine Summable.of_norm_bounded hCsum fun k => ?_
  have hfact_pos : (0 : ℝ) < (Nat.factorial k : ℝ) := by
    exact_mod_cast Nat.factorial_pos k
  have hnormK : ‖((k + 1 : ℕ) : ℂ)‖ = ((k + 1 : ℕ) : ℝ) := norm_natCast _
  have hP : ‖a + b * (↑(k + 1) : ℂ)‖ ≤ (‖a‖ + ‖b‖) * ((k + 1 : ℕ) : ℝ) := by
    have h := norm_add_le a (b * (↑(k + 1) : ℂ))
    rw [norm_mul, hnormK] at h
    have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
      have h1n : (1 : ℕ) ≤ k + 1 := Nat.le_add_left 1 k
      exact_mod_cast h1n
    have hAle : ‖a‖ ≤ ‖a‖ * ((k + 1 : ℕ) : ℝ) :=
      le_mul_of_one_le_right (norm_nonneg _) hk1
    calc ‖a + b * (↑(k + 1) : ℂ)‖ ≤ ‖a‖ + ‖b‖ * ((k + 1 : ℕ) : ℝ) := h
      _ ≤ ‖a‖ * ((k + 1 : ℕ) : ℝ) + ‖b‖ * ((k + 1 : ℕ) : ℝ) := by linarith
      _ = (‖a‖ + ‖b‖) * ((k + 1 : ℕ) : ℝ) := by ring
  have hNatLe : k + 1 ≤ 2 ^ (k + 1) := Nat.le_of_lt (Nat.lt_two_pow_self)
  have hRealLe : ((k + 1 : ℕ) : ℝ) ≤ ((2 ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast hNatLe
  have h2cast : ((2 ^ (k + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (k + 1) := by push_cast; ring
  have hpoly : ((k + 1 : ℕ) : ℝ) ^ n ≤ ((2 : ℝ) ^ (k + 1)) ^ n := by
    rw [← h2cast]
    exact pow_le_pow_left₀ (by positivity) hRealLe n
  have h2eq : ((2 : ℝ) ^ (k + 1)) ^ n = (2 ^ n) ^ (k + 1) := by
    rw [← pow_mul, ← pow_mul, mul_comm]
  have hPn : ‖a + b * (↑(k + 1) : ℂ)‖ ^ n ≤ (‖a‖ + ‖b‖) ^ n * (2 ^ n) ^ (k + 1) := by
    calc ‖a + b * (↑(k + 1) : ℂ)‖ ^ n ≤ ((‖a‖ + ‖b‖) * ((k + 1 : ℕ) : ℝ)) ^ n :=
      pow_le_pow_left₀ (norm_nonneg _) hP n
      _ = (‖a‖ + ‖b‖) ^ n * ((k + 1 : ℕ) : ℝ) ^ n := by rw [mul_pow]
      _ ≤ (‖a‖ + ‖b‖) ^ n * (((2 : ℝ) ^ (k + 1)) ^ n) := by
        apply mul_le_mul_of_nonneg_left hpoly (pow_nonneg (by positivity) n)
      _ = (‖a‖ + ‖b‖) ^ n * (2 ^ n) ^ (k + 1) := by rw [h2eq]
  have hnorm : ‖(a + b * (↑(k + 1) : ℂ)) ^ n * x ^ (k + 1) / (↑(Nat.factorial k) : ℂ)‖
    = ‖a + b * (↑(k + 1) : ℂ)‖ ^ n * ‖x‖ ^ (k + 1) / (Nat.factorial k : ℝ) := by
    rw [norm_div, norm_mul, norm_pow, norm_pow, norm_natCast]
  rw [hnorm]
  have h2succ : (2 ^ n : ℝ) ^ (k + 1) = 2 ^ n * (2 ^ n) ^ k := pow_succ' _ _
  have hXsucc : ‖x‖ ^ (k + 1) = ‖x‖ * ‖x‖ ^ k := pow_succ' _ _
  calc ‖a + b * (↑(k + 1) : ℂ)‖ ^ n * ‖x‖ ^ (k + 1) / (Nat.factorial k : ℝ)
    ≤ ((‖a‖ + ‖b‖) ^ n * (2 ^ n) ^ (k + 1)) * ‖x‖ ^ (k + 1) / (Nat.factorial k : ℝ) := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hfact_pos)
      exact mul_le_mul_of_nonneg_right hPn (pow_nonneg (norm_nonneg _) _)
    _ = (‖a‖ + ‖b‖) ^ n * 2 ^ n * ‖x‖ * ((2 ^ n * ‖x‖) ^ k / (Nat.factorial k : ℝ)) := by
      rw [h2succ, hXsucc, mul_pow]
      ring

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry9IiGeneralizedbellgeneratingDefining

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry9IiGeneralizedbellgeneratingDefining

/--
[ramanujan_part1_ch3_entry9_ii_generalizedbellgenerating_defining](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry9IiGeneralizedbellgeneratingDefining.lean)
-/
@[path]
lemma ramanujan_part1_ch3_entry9_ii_generalizedbellgenerating_defining
  {a b x : ℂ}
  {n : ℕ} :
-- imply
  HasSum (fun k : ℕ => (a + b * (↑(k + 1) : ℂ)) ^ n * x ^ (k + 1) / (↑(Nat.factorial k) : ℂ))
    (Complex.exp x * generalizedBellGenerating a b x n) := by
-- proof
  have hSumm : Summable
    (fun k : ℕ => (a + b * (↑(k + 1) : ℂ)) ^ n * x ^ (k + 1) / (↑(Nat.factorial k) : ℂ)) :=
    summable_bellTerm a b x n
  have hexp : Complex.exp x * Complex.exp (-x) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hEq : Complex.exp x * (Complex.exp (-x) *
    ∑' k : ℕ, (a + b * (↑(k + 1) : ℂ)) ^ n * x ^ (k + 1) / (↑(Nat.factorial k) : ℂ)) =
    ∑' k : ℕ, (a + b * (↑(k + 1) : ℂ)) ^ n * x ^ (k + 1) / (↑(Nat.factorial k) : ℂ) := by
    rw [← mul_assoc, hexp, one_mul]
  unfold generalizedBellGenerating
  rwa [hEq]

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry9IiGeneralizedbellgeneratingDefining


-- created on 2026-10-20
-- updated on 2026-10-23
