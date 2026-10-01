import sympy.functions.elementary.complexes
import sympy.Basic
open Real


@[main]
private lemma simp.exp
  {z : ℂ} :
-- imply
  arg (Complex.exp (Complex.I * arg z)) = arg z := by
-- proof
  rw [mul_comm, Complex.arg_exp_mul_I, toIocMod_eq_self]
  exact ⟨Complex.neg_pi_lt_arg z, by linarith [Complex.arg_le_pi z, Real.pi_pos]⟩


-- created on 2019-03-01
