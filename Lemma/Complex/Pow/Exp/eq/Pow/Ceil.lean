import sympy.functions.elementary.complexes
import sympy.Basic
open Real


@[main]
private lemma main
  {x : ℝ}
  {n : ℕ} :
-- imply
  Complex.exp (Complex.I * x) ^ (1 / (n : ℂ)) = Complex.exp (Complex.I * (x - ⌈x / (2 * π) - 1 / 2⌉ * π * 2) / n) := by
-- proof
  have hne := Complex.exp_ne_zero (Complex.I * x)
  rw [Complex.cpow_def_of_ne_zero hne]
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp (Complex.exp_log hne)
  have him := congrArg Complex.im hk
  simp only [Complex.log_im, Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] at him
  norm_num at him
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have b1 := Complex.neg_pi_lt_arg (Complex.exp (Complex.I * x))
  have b2 := Complex.arg_le_pi (Complex.exp (Complex.I * x))
  have hm : ⌈x / (2 * π) - 1 / 2⌉ = -k := by
    rw [Int.ceil_eq_iff]
    have e : x / (2 * π) - 1 / 2 = arg (Complex.exp (Complex.I * x)) / (2 * π) - k - 1 / 2 := by
      rw [him]; field_simp; ring
    have c1 : -1 / 2 < arg (Complex.exp (Complex.I * x)) / (2 * π) := by rw [lt_div_iff₀ (by positivity)]; linarith
    have c2 : arg (Complex.exp (Complex.I * x)) / (2 * π) ≤ 1 / 2 := by rw [div_le_iff₀ (by positivity)]; linarith
    rw [e]
    push_cast
    constructor <;> linarith
  rw [hk, hm]
  congr 1
  push_cast
  ring


-- created on 2020-03-02
