import Mathlib
import Initialize.Tactic.Attr.Basic
open Complex ModularGroup
open UpperHalfPlane hiding I
open scoped ModularForm MatrixGroups Real Topology


noncomputable def logEta (z : ℂ) : ℂ := π * I * z / 12 + ∑' n : ℕ, log (1 - ModularForm.eta_q n z)

private lemma norm_eta_q (n : ℕ) (z : ℂ) : ‖ModularForm.eta_q n z‖ = Real.exp (-(2 * π * (n + 1) * z.im)) := by
  rw [ModularForm.eta_q_eq_cexp, norm_exp]
  congr 1
  simp [mul_re, mul_im]

private lemma norm_eta_q_lt_one (n : ℕ) {z : ℂ} (hz : 0 < z.im) : ‖ModularForm.eta_q n z‖ < 1 := by
  rw [norm_eta_q, Real.exp_lt_one_iff]
  have : 0 < 2 * π * (n + 1) * z.im := by positivity
  linarith

private lemma one_sub_eta_q_mem_slitPlane (n : ℕ) {z : ℂ} (hz : 0 < z.im) :
  1 - ModularForm.eta_q n z ∈ slitPlane := by
  rw [sub_eq_add_neg]
  exact mem_slitPlane_of_norm_lt_one (by rw [norm_neg]; exact norm_eta_q_lt_one n hz)

private lemma summable_log (z : ℍ) : Summable fun n : ℕ => log (1 - ModularForm.eta_q n z) := by
  have h := Complex.summable_log_one_add_of_summable (Summable.of_norm (ModularForm.summable_eta_q z))
  simpa [sub_eq_add_neg] using h

private lemma exp_logEta (z : ℍ) : exp (logEta z) = η (z : ℂ) := by
  rw [logEta, exp_add, ModularForm.eta,
    ← Complex.cexp_tsum_eq_tprod (fun n => ModularForm.one_sub_eta_q_ne_zero n z.2) (summable_log z)]
  congr 1
  rw [Function.Periodic.qParam]
  congr 1
  push_cast
  ring
/--
[ModularForm_exp_logEta](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularForm_exp_logEta.lean)
-/
@[path]
private lemma main
  {z : UpperHalfPlane} :
-- imply
  Complex.exp (Real.pi * Complex.I * (z : ℂ) / 12 + ∑' n : ℕ, Complex.log (1 - ModularForm.eta_q n (z : ℂ))) = ModularForm.eta z :=
-- proof
  exp_logEta z


-- created on 2026-10-23
