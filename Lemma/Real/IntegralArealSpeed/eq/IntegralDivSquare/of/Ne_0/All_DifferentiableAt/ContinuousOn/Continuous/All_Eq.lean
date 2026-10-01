import Lemma.Real.ArealSpeed.eq.Mul.of.Ne_0
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import sympy.physics.vector.kinematics
import sympy.Basic


/--
Change of variables from time to angle.  With \(\rho(t)=r(\theta(t))\) and
\(\dfrac{ds}{dt}=\tfrac12\rho^2\dot\theta\), the area swept during \([0,T]\) is
\[
\int_0^T\frac{ds}{dt}\,dt=\int_{\theta(0)}^{\theta(T)}\tfrac12 r(\varphi)^2\,d\varphi.
\]
-/
@[main]
private lemma main
  {m T : ℝ}
  {r ρ θ : ℝ → ℝ}
-- given
  (hm : m ≠ 0)
  (hθ : ∀ t ∈ Set.uIcc 0 T, DifferentiableAt ℝ θ t)
  (hθ' : ContinuousOn (deriv θ) (Set.uIcc 0 T))
  (hr : Continuous r)
  (hρ : ∀ t, ρ t = r (θ t)) :
-- imply
  ∫ t in (0 : ℝ)..T, areal_speed m ρ θ t = ∫ φ in θ 0..θ T, (r φ) ^ 2 / 2 := by
-- proof
  have h : ∀ t, areal_speed m ρ θ t = (fun φ => (r φ) ^ 2 / 2) (θ t) * deriv θ t := by
    intro t
    rw [Real.ArealSpeed.eq.Mul.of.Ne_0 hm, hρ]
    ring
  simp only [h]
  exact intervalIntegral.integral_comp_mul_deriv (f := θ) (f' := deriv θ)
    (g := fun φ => (r φ) ^ 2 / 2) (fun t ht => (hθ t ht).hasDerivAt) hθ'
    (by fun_prop)


-- created on 2026-09-29