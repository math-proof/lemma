import sympy.physics.vector.kinematics
import sympy.Basic


/--
Notes (**): reciprocal radius equals the phase-zero Kepler ansatz
\(1/r=A\cos\theta+Cm/J^2\).
-/
@[main]
private lemma main
  {r : ℝ → ℝ}
  {A C m J : ℝ} :
-- imply
  binet_w r = kepler_orbit_reciprocal A C m J ↔
    ∀ φ, (r φ)⁻¹ = A * Real.cos φ + C * m / J ^ 2 := by
-- proof
  constructor
  · intro h φ
    simpa [binet_w, kepler_orbit_reciprocal] using congrArg (fun f => f φ) h
  · intro h
    funext φ
    simpa [binet_w, kepler_orbit_reciprocal] using h φ


-- created on 2026-09-29
