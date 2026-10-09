import sympy.functions.elementary.complexes
import sympy.Basic


@[path]
private lemma cubic_root
  {p : ℂ} :
-- imply
  (p ^ 3) ^ (1 / 3 : ℂ) = p * Complex.exp (-Complex.I * 2 * π / 3 * ⌈3 * arg p / (2 * π) - 1 / 2⌉) := by
-- proof
  by_cases hp : p = 0
  · subst hp
    simp
  have h3 : p ^ 3 ≠ 0 := pow_ne_zero 3 hp
  rw [Complex.cpow_def_of_ne_zero h3]
  have e : Complex.exp (Complex.log (p ^ 3)) = Complex.exp (3 * Complex.log p) := by
    rw [Complex.exp_log h3, show (3 : ℂ) * Complex.log p = ((3 : ℕ) : ℂ) * Complex.log p by norm_num, Complex.exp_nat_mul, Complex.exp_log hp]
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp e
  have him := congrArg Complex.im hk
  simp only [Complex.log_im, Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.log_re] at him
  norm_num at him
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have b1 := Complex.neg_pi_lt_arg (p ^ 3)
  have b2 := Complex.arg_le_pi (p ^ 3)
  have hm : ⌈3 * arg p / (2 * π) - 1 / 2⌉ = -k := by
    rw [Int.ceil_eq_iff]
    have e : 3 * arg p / (2 * π) - 1 / 2 = arg (p ^ 3) / (2 * π) - k - 1 / 2 := by
      rw [him]; field_simp; ring
    have c1 : -1 / 2 < arg (p ^ 3) / (2 * π) := by rw [lt_div_iff₀ (by positivity)]; linarith
    have c2 : arg (p ^ 3) / (2 * π) ≤ 1 / 2 := by rw [div_le_iff₀ (by positivity)]; linarith
    rw [e]
    push_cast
    constructor <;> linarith
  rw [hk, hm]
  have e2 : (3 * Complex.log p + ↑k * (2 * ↑π * Complex.I)) * (1 / 3) = Complex.log p + -Complex.I * 2 * ↑π / 3 * ↑(-k) := by
    push_cast; ring
  rw [e2, Complex.exp_add, Complex.exp_log hp]


-- created on 2020-03-11
