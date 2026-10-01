import sympy.functions.elementary.complexes
import sympy.Basic
open Real


@[main]
private lemma cubic_root
  {A B : ℂ}
-- given
  (h₀ : A ^ 3 = B ^ 3)
  (h₁ : ⌈3 * arg A / (π * 2) - 1 / 2⌉ = ⌈3 * arg B / (π * 2) - 1 / 2⌉) :
-- imply
  A = B := by
-- proof
  by_cases hA : A = 0
  · subst hA
    have : B ^ 3 = 0 := by rw [← h₀]; ring
    exact (pow_eq_zero_iff (by norm_num)).mp this |>.symm
  by_cases hB : B = 0
  · subst hB
    have : A ^ 3 = 0 := by rw [h₀]; ring
    exact absurd ((pow_eq_zero_iff (by norm_num)).mp this) hA
  have e : Complex.exp (3 * Complex.log A) = Complex.exp (3 * Complex.log B) := by
    have e3 : ∀ z : ℂ, z ≠ 0 → Complex.exp (3 * Complex.log z) = z ^ 3 := fun z hz => by
      rw [show (3 : ℂ) * Complex.log z = ((3 : ℕ) : ℂ) * Complex.log z by norm_num, Complex.exp_nat_mul, Complex.exp_log hz]
    rw [e3 A hA, e3 B hB, h₀]
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp e
  have him := congrArg Complex.im hn
  simp only [Complex.mul_im, Complex.log_im, Complex.add_im, Complex.log_re, Complex.intCast_re, Complex.intCast_im,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] at him
  norm_num at him
  have hp : (0 : ℝ) < π := Real.pi_pos
  have ht : 3 * arg A / (π * 2) - 1 / 2 = (3 * arg B / (π * 2) - 1 / 2) + (n : ℝ) := by
    rw [him]; field_simp; ring
  rw [ht, Int.ceil_add_intCast] at h₁
  have hn0 : n = 0 := by omega
  subst hn0
  simp at hn
  rw [← Complex.exp_log hA, ← Complex.exp_log hB, hn]


-- created on 2026-09-27
