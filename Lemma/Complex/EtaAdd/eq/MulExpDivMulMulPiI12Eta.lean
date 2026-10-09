import Mathlib
import sympy.Basic

open Complex ModularGroup
open UpperHalfPlane hiding I
open scoped ModularForm MatrixGroups Real

/--
[ModularForm_eta_add_intCast](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularForm_eta_add_intCast.lean)
-/

lemma eta_add_int (z : ℂ) (m : ℤ) : η (z + m) = cexp (π * I * m / 12) * η z := by
  unfold ModularForm.eta
  have hq : Function.Periodic.qParam 24 (z + m) = cexp (π * I * m / 12) * Function.Periodic.qParam 24 z := by
    simp only [Function.Periodic.qParam, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hp : (fun n => 1 - ModularForm.eta_q n (z + m)) = fun n => 1 - ModularForm.eta_q n z := by
    funext n
    rw [ModularForm.eta_q_eq_cexp, ModularForm.eta_q_eq_cexp]
    congr 1
    rw [show 2 * π * I * (n + 1) * (z + m) = 2 * π * I * (n + 1) * z + ((n + 1) * m : ℤ) * (2 * π * I) by
      push_cast; ring, Complex.exp_add, exp_int_mul_two_pi_mul_I, mul_one]
  rw [hq, hp]
  ring
@[path]
private lemma main
  {z : ℂ}
  {m : ℤ} :
-- imply
  ModularForm.eta (z + m) = Complex.exp (Real.pi * Complex.I * m / 12) * ModularForm.eta z :=
-- proof
  eta_add_int z m


-- created on 2026-10-05
