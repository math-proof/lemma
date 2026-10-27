import Mathlib
import Initialize.Tactic.Attr.Basic
open Complex ModularGroup
open UpperHalfPlane hiding I
open scoped ModularForm MatrixGroups Real Topology


noncomputable def logEta (z : ℂ) : ℂ := π * I * z / 12 + ∑' n : ℕ, log (1 - ModularForm.eta_q n z)

private lemma logEta_add_int (z : ℂ) (m : ℤ) : logEta (z + m) = logEta z + π * I * m / 12 := by
  have hq : ∀ n : ℕ, ModularForm.eta_q n (z + m) = ModularForm.eta_q n z := by
    intro n
    have hmul : 2 * π * I * (n + 1) * (z + m) =
        2 * π * I * (n + 1) * z + ((n + 1) * m : ℤ) * (2 * π * I) := by
      push_cast
      ring
    rw [ModularForm.eta_q_eq_cexp, ModularForm.eta_q_eq_cexp, hmul,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  simp only [logEta, hq]
  ring

/--
[ModularForm_logEta_add_intCast](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularForm_logEta_add_intCast.lean)
-/
@[path]
private lemma main
  {z : ℂ}
  {m : ℤ} :
-- imply
  (Real.pi * Complex.I * (z + m) / 12 + ∑' n : ℕ, Complex.log (1 - ModularForm.eta_q n (z + m))) = (Real.pi * Complex.I * z / 12 + ∑' n : ℕ, Complex.log (1 - ModularForm.eta_q n z)) + Real.pi * Complex.I * m / 12 :=
-- proof
  logEta_add_int z m


-- created on 2026-10-23
