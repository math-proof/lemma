import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[LanglandsTunnell_forall_cpow_mul_eval_eq_of_forall_lt_re](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_LanglandsTunnell_forall_cpow_mul_eval_eq_of_forall_lt_re.lean)
-/
@[path]
private lemma main
  (N : ℕ)
  (P Q : Polynomial ℂ)
  (m n : ℤ)
  (c : ℝ)
  -- given
  (hN : 1 < N)
  (h : ∀ u : ℂ, c < u.re → (N : ℂ) ^ ((m : ℂ) * u) * P.eval ((N : ℂ) ^ (-u)) = (N : ℂ) ^ ((n : ℂ) * u) * Q.eval ((N : ℂ) ^ (-u))) :
  -- imply
  ∀ u : ℂ, (N : ℂ) ^ ((m : ℂ) * u) * P.eval ((N : ℂ) ^ (-u)) = (N : ℂ) ^ ((n : ℂ) * u) * Q.eval ((N : ℂ) ^ (-u)) := by
  -- proof
  have hN0 : (N : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : N ≠ 0)
  have hdcpow : ∀ a : ℂ, Differentiable ℂ (fun u : ℂ => (N : ℂ) ^ (a * u)) := by
    intro a
    have : (fun u : ℂ => (N : ℂ) ^ (a * u)) = fun u => Complex.exp (Complex.log (N : ℂ) * (a * u)) := by
      funext u
      rw [Complex.cpow_def_of_ne_zero hN0]
    rw [this]
    apply Complex.differentiable_exp.comp ((differentiable_const _).mul ((differentiable_const _).mul differentiable_id))
  have hdneg : Differentiable ℂ (fun u : ℂ => (N : ℂ) ^ (-u)) := by
    have := hdcpow (-1)
    simpa using this
  have hdeval : ∀ R : Polynomial ℂ, Differentiable ℂ (fun u : ℂ => R.eval ((N : ℂ) ^ (-u))) :=
    fun R => (Polynomial.differentiable R).comp hdneg
  set f : ℂ → ℂ := fun u => (N : ℂ) ^ ((m : ℂ) * u) * P.eval ((N : ℂ) ^ (-u)) - (N : ℂ) ^ ((n : ℂ) * u) * Q.eval ((N : ℂ) ^ (-u)) with hf
  have hdf : Differentiable ℂ f := ((hdcpow m).mul (hdeval P)).sub ((hdcpow n).mul (hdeval Q))
  have han : AnalyticOnNhd ℂ f Set.univ := (hdf.differentiableOn).analyticOnNhd isOpen_univ
  set z₀ : ℂ := ((c + 1 : ℝ) : ℂ) with hz₀
  have hopen : IsOpen {u : ℂ | c < u.re} := isOpen_lt continuous_const Complex.continuous_re
  have hz₀mem : z₀ ∈ {u : ℂ | c < u.re} := by
    show c < z₀.re
    rw [hz₀, Complex.ofReal_re]
    linarith
  have hev : ∀ᶠ u in nhds z₀, f u = (0 : ℂ → ℂ) u := by
    filter_upwards [hopen.mem_nhds hz₀mem] with u hu
    simp only [hf, Pi.zero_apply, sub_eq_zero]
    apply h u hu
  have hzero := han.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const isPreconnected_univ (Set.mem_univ z₀) hev
  intro u
  have this := hzero (Set.mem_univ u)
  simp only [hf] at this
  apply sub_eq_zero.mp this


-- created on 2026-10-20
