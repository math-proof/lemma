import sympy.functions.elementary.complexes
import sympy.Basic
import Lemma.Complex.AddDivNeg1'2DivMulISqrt3'2.eq.ExpMulDivMul2Pi3I
import Lemma.Complex.PowPow_Div1'3'3.eq.Self
import Lemma.Complex.SquarePow_Div1'2.eq.Self
open Complex


/-- The core identity: with the SymPy branch index `d`, `A * B * ω ^ d = -p / 3`. -/
@[path]
private lemma main
  {p q δ : ℂ}
  {d : ℤ}
-- given
  (hδ : δ = 4 * p ^ 3 / 27 + q ^ 2)
  (h₀ : ⌈3 * arg (-p / 3) / (π * 2) - 1 / 2⌉ - (if p * (⌈(arg (δ ^ (1 / 2 : ℂ) - q) + arg (-δ ^ (1 / 2 : ℂ) - q)) / (2 * π) - 1 / 2⌉ : ℂ) = 0 then 0 else if arg (δ ^ (1 / 2 : ℂ) - q) + arg (-δ ^ (1 / 2 : ℂ) - q) > π then 1 else -1) = d) :
-- imply
  (δ ^ (1 / 2 : ℂ) / 2 - q / 2) ^ (1 / 3 : ℂ) * (-δ ^ (1 / 2 : ℂ) / 2 - q / 2) ^ (1 / 3 : ℂ) * (-1 / 2 + Complex.I * √3 / 2) ^ d = -p / 3 := by
-- proof
  set s := δ ^ (1 / 2 : ℂ) with hs_def
  set A := (s / 2 - q / 2) ^ (1 / 3 : ℂ) with hA_def
  set B := (-s / 2 - q / 2) ^ (1 / 3 : ℂ) with hB_def
  set ω : ℂ := -1 / 2 + Complex.I * √3 / 2 with hω_def
  set W := ω ^ d with hW_def
  have hs : s ^ 2 = δ := SquarePow_Div1'2.eq.Self δ
  have hA3 : A ^ 3 = s / 2 - q / 2 := PowPow_Div1'3'3.eq.Self _
  have hB3 : B ^ 3 = -s / 2 - q / 2 := PowPow_Div1'3'3.eq.Self _
  have hAB3 : (A * B) ^ 3 = (-p / 3) ^ 3 := by
    rw [mul_pow, hA3, hB3]
    linear_combination (-1 / 4 : ℂ) * hs + (-1 / 4 : ℂ) * hδ
  have hω : ω = Complex.exp (↑(2 * π / 3) * Complex.I) := AddDivNeg1'2DivMulISqrt3'2.eq.ExpMulDivMul2Pi3I
  by_cases hp : p = 0
  ·
    subst hp
    have : (A * B) ^ 3 = 0 := by rw [hAB3]; ring
    rw [(pow_eq_zero_iff (by norm_num)).mp this]
    ring
  have hc : -p / 3 ≠ 0 := by
    intro h; apply hp; linear_combination -3 * h
  have ha0 : s / 2 - q / 2 ≠ 0 := by
    intro h
    apply hc
    have : (-p / 3) ^ 3 = 0 := by rw [← hAB3, mul_pow, hA3, h]; ring
    exact (pow_eq_zero_iff (by norm_num)).mp this
  have hb0 : -s / 2 - q / 2 ≠ 0 := by
    intro h
    apply hc
    have : (-p / 3) ^ 3 = 0 := by rw [← hAB3, mul_pow, hB3, h]; ring
    exact (pow_eq_zero_iff (by norm_num)).mp this
  have hAB : A * B = Complex.exp ((Complex.log (s / 2 - q / 2) + Complex.log (-s / 2 - q / 2)) / 3) := by
    rw [hA_def, hB_def, Complex.cpow_def_of_ne_zero ha0, Complex.cpow_def_of_ne_zero hb0, ← Complex.exp_add]
    ring_nf
  have e : Complex.exp (Complex.log (s / 2 - q / 2) + Complex.log (-s / 2 - q / 2)) = Complex.exp (3 * Complex.log (-p / 3)) := by
    rw [Complex.exp_add, Complex.exp_log ha0, Complex.exp_log hb0, show (3 : ℂ) * Complex.log (-p / 3) = ((3 : ℕ) : ℂ) * Complex.log (-p / 3) by norm_num, Complex.exp_nat_mul, Complex.exp_log hc]
    have := hAB3
    rw [mul_pow, hA3, hB3] at this
    exact_mod_cast this
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp e
  have him := congrArg Complex.im hn
  simp only [Complex.log_im, Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.log_re] at him
  norm_num at him
  have hU : arg (s / 2 - q / 2) = arg (s - q) := by
    have : s / 2 - q / 2 = ((1 / 2 : ℝ) : ℂ) * (s - q) := by push_cast; ring
    rw [this, Complex.arg_real_mul _ (by norm_num)]
  have hV : arg (-s / 2 - q / 2) = arg (-s - q) := by
    have : -s / 2 - q / 2 = ((1 / 2 : ℝ) : ℂ) * (-s - q) := by push_cast; ring
    rw [this, Complex.arg_real_mul _ (by norm_num)]
  rw [hU, hV] at him
  have hpi : (0 : ℝ) < π := Real.pi_pos
  set α := arg (s - q)
  set β := arg (-s - q)
  have hpiece : (if p * (⌈(α + β) / (2 * π) - 1 / 2⌉ : ℂ) = 0 then (0 : ℤ) else if α + β > π then 1 else -1) = ⌈(α + β) / (2 * π) - 1 / 2⌉ := by
    have hα1 := Complex.neg_pi_lt_arg (s - q)
    have hα2 := Complex.arg_le_pi (s - q)
    have hβ1 := Complex.neg_pi_lt_arg (-s - q)
    have hβ2 := Complex.arg_le_pi (-s - q)
    by_cases h0 : ⌈(α + β) / (2 * π) - 1 / 2⌉ = 0
    · rw [h0]; simp
    have hne : p * (⌈(α + β) / (2 * π) - 1 / 2⌉ : ℂ) ≠ 0 := mul_ne_zero hp (by exact_mod_cast h0)
    rw [if_neg hne]
    if hgt : α + β > π then
      rw [if_pos hgt]
      have h1 : 1 / 2 < (α + β) / (2 * π) := by rw [lt_div_iff₀ (by positivity)]; linarith
      have h2 : (α + β) / (2 * π) ≤ 1 := by rw [div_le_iff₀ (by positivity)]; linarith
      symm
      rw [Int.ceil_eq_iff]
      constructor <;> push_cast <;> linarith
    else
      rw [if_neg hgt]
      have h3 : (α + β) / (2 * π) ≤ 1 / 2 := by rw [div_le_iff₀ (by positivity)]; linarith
      have h4 : -1 < (α + β) / (2 * π) := by rw [lt_div_iff₀ (by positivity)]; linarith
      have hle : ⌈(α + β) / (2 * π) - 1 / 2⌉ ≤ 0 := by
        rw [Int.ceil_le]
        push_cast
        linarith
      have hge : -1 ≤ ⌈(α + β) / (2 * π) - 1 / 2⌉ := by
        rw [Int.le_ceil_iff]
        push_cast
        linarith
      omega
  rw [hpiece] at h₀
  have ht : (α + β) / (2 * π) - 1 / 2 = (3 * arg (-p / 3) / (π * 2) - 1 / 2) + (n : ℝ) := by
    rw [him]; field_simp; ring
  rw [ht, Int.ceil_add_intCast] at h₀
  have hd : d = -n := by omega
  rw [hAB, hW_def, hd, hn, hω]
  have : (3 * Complex.log (-p / 3) + ↑n * (2 * ↑π * Complex.I)) / 3 = Complex.log (-p / 3) + ↑n * (↑(2 * π / 3) * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_log hc, Complex.exp_int_mul, zpow_neg, mul_assoc, mul_inv_cancel₀ (zpow_ne_zero _ (Complex.exp_ne_zero _)), mul_one]


-- created on 2026-10-07
