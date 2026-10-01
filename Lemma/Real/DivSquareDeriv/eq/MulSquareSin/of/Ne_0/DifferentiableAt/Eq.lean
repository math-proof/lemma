import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import sympy.physics.vector.kinematics
import sympy.Basic


/--
From \(1/r=-Cm/J^2+A\cos\theta\):
\(\dfrac{1}{r^4}\left(\dfrac{dr}{d\theta}\right)^2=A^2\sin^2\theta\).
-/
@[main]
private lemma main
  {r : ℝ → ℝ}
  {A C m J φ : ℝ}
-- given
  (hr0 : r φ ≠ 0)
  (hr : DifferentiableAt ℝ r φ)
  (horb : binet_w r = kepler_orbit_reciprocal_signed A C m J) :
-- imply
  (deriv r φ) ^ 2 / (r φ) ^ 4 = A ^ 2 * Real.sin φ ^ 2 := by
-- proof
  have heq : ∀ ψ, binet_w r ψ = A * Real.cos ψ + (-C) * m / J ^ 2 := by
    intro ψ
    simpa [kepler_orbit_reciprocal_signed, kepler_orbit_reciprocal] using
      congrArg (fun f => f ψ) horb
  have hw' : deriv (binet_w r) φ = -deriv r φ / (r φ) ^ 2 := by
    change deriv (fun ψ => (r ψ)⁻¹) φ = _
    exact (hr.hasDerivAt.inv hr0).deriv
  have hrhs :
      HasDerivAt (fun ψ => A * Real.cos ψ + (-C) * m / J ^ 2) (-A * Real.sin φ) φ := by
    have hc := (Real.hasDerivAt_cos φ).const_mul A
    have h0 := hasDerivAt_const φ ((-C) * m / J ^ 2)
    exact (hc.add h0).congr_deriv (by ring)
  have hder : deriv (binet_w r) φ = -A * Real.sin φ := by
    have heq' : binet_w r = fun ψ => A * Real.cos ψ + (-C) * m / J ^ 2 := funext heq
    rw [heq']
    exact hrhs.deriv
  have hquot : deriv r φ / (r φ) ^ 2 = A * Real.sin φ := by
    have hneg : -deriv r φ / (r φ) ^ 2 = -A * Real.sin φ := by
      rw [← hw', hder]
    exact neg_inj.mp (by simpa [neg_div] using hneg)
  have hr2 : (r φ) ^ 2 ≠ 0 := pow_ne_zero 2 hr0
  have hpow : (deriv r φ) ^ 2 / (r φ) ^ 4 = (deriv r φ / (r φ) ^ 2) ^ 2 := by
    field_simp [hr2]
    try ring
  rw [hpow, hquot]
  ring


-- created on 2026-09-29
