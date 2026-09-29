import sympy.physics.vector.kinematics
import sympy.Basic


/--
Notes orbit form with \(A=(Cm/J^2)e\) and \(p=-J^2/(Cm)\):
\[
r=\frac{p}{1-e\cos\theta}.
\]
-/
@[main]
private lemma main
  {A C m J e p φ : ℝ}
-- given
  (hJ : J ≠ 0)
  (_hCm : C * m ≠ 0)
  (hden : 1 - e * Real.cos φ ≠ 0)
  (hA : A = C * m / J ^ 2 * e)
  (hp : p = semi_latus_rectum C m J) :
-- imply
  (kepler_orbit_reciprocal_signed A C m J φ)⁻¹ = p / (1 - e * Real.cos φ) := by
-- proof
  have hJ2 : J ^ 2 ≠ 0 := pow_ne_zero 2 hJ
  have hform :
      kepler_orbit_reciprocal_signed A C m J φ =
        -(C * m / J ^ 2) * (1 - e * Real.cos φ) := by
    simp only [kepler_orbit_reciprocal_signed, kepler_orbit_reciprocal, hA]
    ring
  rw [hform, hp, semi_latus_rectum]
  field_simp [hJ2, _hCm, hden]
  try ring


-- created on 2026-09-29
