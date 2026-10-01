import Lemma.Real.Deriv.eq.Div_Mul_Square.of.Ne_0.Ne_0.EqAngularMomentum
import Lemma.Real.MechanicalEnergy.eq.Add.of.DifferentiableAt.DifferentiableAt
import sympy.physics.vector.kinematics
import sympy.Basic


/--
With \(J=m\rho^2\dot\theta\) and chain rule \(\dot\rho=(d\rho/d\theta)\dot\theta\),
\[
E=\frac{J^2}{2m\rho^4}\left(\frac{d\rho}{d\theta}\right)^2+\frac{J^2}{2m\rho^2}+\frac{C}{\rho}.
\]
Here `r` is radius as a function of angle, and \(\rho=r\circ\theta\).
-/
@[main]
private lemma main
  {m C J : ℝ}
  {r θ : ℝ → ℝ}
  {t : ℝ}
-- given
  (hm : m ≠ 0)
  (hρ : r (θ t) ≠ 0)
  (hθ : DifferentiableAt ℝ θ t)
  (_hr : DifferentiableAt ℝ r (θ t))
  (hρt : DifferentiableAt ℝ (r ∘ θ) t)
  (hJ : angular_momentum m (r ∘ θ) θ t = J)
  (hchain : deriv (r ∘ θ) t = deriv r (θ t) * deriv θ t) :
-- imply
  mechanical_energy m C (r ∘ θ) θ t = mechanical_energy_of_angle m C J r (θ t) := by
-- proof
  have hE := Real.MechanicalEnergy.eq.Add.of.DifferentiableAt.DifferentiableAt (m := m) (C := C)
    hρt hθ
  have hθdot :=
    Real.Deriv.eq.Div_Mul_Square.of.Ne_0.Ne_0.EqAngularMomentum
      (ρ := r ∘ θ) (θ := θ) (t := t) hm (by simpa using hρ) hJ
  rw [hE, hchain, hθdot]
  simp only [mechanical_energy_of_angle, Function.comp_apply]
  have hr2 : (r (θ t)) ^ 2 ≠ 0 := pow_ne_zero 2 hρ
  have hr4 : (r (θ t)) ^ 4 ≠ 0 := pow_ne_zero 4 hρ
  field_simp [hm, hr2, hr4]
  try ring


-- created on 2026-09-29
