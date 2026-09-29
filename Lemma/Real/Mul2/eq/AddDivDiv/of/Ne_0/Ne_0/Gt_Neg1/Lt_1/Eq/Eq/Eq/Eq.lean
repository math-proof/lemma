import Lemma.Real.InvKeplerOrbitReciprocalSigned.eq.Div.of.Ne_0.Ne_0.Ne_0.Eq.Eq
import sympy.physics.vector.kinematics
import sympy.Basic
open Real


/--
Perigee/apogee distances of the signed Kepler orbit \(1/r=-\dfrac{Cm}{J^2}(1-e\cos\theta)\)
(with \(|e|<1\); the sign of \(e\) only selects the phase):
\(r(0)=\dfrac{p}{1-e}\) and \(r(\pi)=\dfrac{p}{1+e}\), so the major axis is
\(2a=r(0)+r(\pi)=\dfrac{p}{1-e}+\dfrac{p}{1+e}\).
-/
@[main]
private lemma main
  {r : ℝ → ℝ}
  {A C m J e p a : ℝ}
-- given
  (hJ : J ≠ 0)
  (hCm : C * m ≠ 0)
  (he₀ : -1 < e)
  (he₁ : e < 1)
  (hA : A = C * m / J ^ 2 * e)
  (hp : p = semi_latus_rectum C m J)
  (horb : binet_w r = kepler_orbit_reciprocal_signed A C m J)
  (ha : 2 * a = r 0 + r π) :
-- imply
  2 * a = p / (1 - e) + p / (1 + e) := by
-- proof
  have hr : ∀ φ, r φ = (kepler_orbit_reciprocal_signed A C m J φ)⁻¹ := by
    intro φ
    rw [← congrFun horb φ, binet_w, inv_inv]
  have h₀ : 1 - e * Real.cos 0 ≠ 0 := by
    rw [Real.cos_zero]
    linarith
  have h₁ : 1 - e * Real.cos π ≠ 0 := by
    rw [Real.cos_pi]
    linarith
  have hr₀ := Real.InvKeplerOrbitReciprocalSigned.eq.Div.of.Ne_0.Ne_0.Ne_0.Eq.Eq
    (φ := 0) hJ hCm h₀ hA hp
  have hr₁ := Real.InvKeplerOrbitReciprocalSigned.eq.Div.of.Ne_0.Ne_0.Ne_0.Eq.Eq
    (φ := π) hJ hCm h₁ hA hp
  rw [ha, hr 0, hr π, hr₀, hr₁, Real.cos_zero, Real.cos_pi]
  ring


-- created on 2026-09-29