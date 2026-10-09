import Lemma.Real.All_AddDerivDeriv.eq.DivMul.of.Ne_0
import sympy.physics.vector.kinematics
import sympy.Basic


/--
Phase-zero Kepler reciprocal \(A\cos\theta+Cm/J^2\) solves the Binet ODE.
-/
@[path]
private lemma main
  (A C m J : ℝ)
-- given
  (hJ : J ≠ 0) :
-- imply
  ∀ φ,
    deriv (deriv (kepler_orbit_reciprocal A C m J)) φ +
        kepler_orbit_reciprocal A C m J φ =
      C * m / J ^ 2 := by
-- proof
  intro φ
  have h := Real.All_AddDerivDeriv.eq.DivMul.of.Ne_0 A C m J 0 hJ φ
  simp_rw [add_zero] at h
  unfold kepler_orbit_reciprocal
  exact h


-- created on 2026-09-29
