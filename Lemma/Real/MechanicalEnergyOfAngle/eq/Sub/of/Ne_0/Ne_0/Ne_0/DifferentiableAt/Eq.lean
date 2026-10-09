import Lemma.Real.DivSquareDeriv.eq.MulSquareSin.of.Ne_0.DifferentiableAt.Eq
import sympy.physics.vector.kinematics
import sympy.Basic


/--
On the signed Kepler orbit, angle-domain energy is independent of \(\theta\):
\[
E=\dfrac{J^2}{2m}A^2-\dfrac{C^2 m}{2J^2}.
\]
-/
@[path]
private lemma main
  {r : ℝ → ℝ}
  {A C m J φ : ℝ}
-- given
  (hm : m ≠ 0)
  (hJ : J ≠ 0)
  (hr0 : r φ ≠ 0)
  (hr : DifferentiableAt ℝ r φ)
  (horb : binet_w r = kepler_orbit_reciprocal_signed A C m J) :
-- imply
  mechanical_energy_of_angle m C J r φ =
    J ^ 2 / (2 * m) * A ^ 2 - C ^ 2 * m / (2 * J ^ 2) := by
-- proof
  have hsin :=
    Real.DivSquareDeriv.eq.MulSquareSin.of.Ne_0.DifferentiableAt.Eq hr0 hr horb
  have hw : (r φ)⁻¹ = A * Real.cos φ - C * m / J ^ 2 := by
    have h := congrArg (fun f => f φ) horb
    simp only [binet_w, kepler_orbit_reciprocal_signed, kepler_orbit_reciprocal] at h
    convert h using 1
    ring
  have hr2 : (r φ) ^ 2 ≠ 0 := pow_ne_zero 2 hr0
  have hr4 : (r φ) ^ 4 ≠ 0 := pow_ne_zero 4 hr0
  have hm2 : (2 * m) ≠ 0 := mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hm
  have hJ2 : J ^ 2 ≠ 0 := pow_ne_zero 2 hJ
  have htrig : Real.sin φ ^ 2 + Real.cos φ ^ 2 = 1 := Real.sin_sq_add_cos_sq φ
  -- Algebraic core identity
  have hcore :
      J ^ 2 / (2 * m) * (A ^ 2 * Real.sin φ ^ 2) +
          J ^ 2 / (2 * m) * (A * Real.cos φ - C * m / J ^ 2) ^ 2 +
            C * (A * Real.cos φ - C * m / J ^ 2) =
        J ^ 2 / (2 * m) * A ^ 2 - C ^ 2 * m / (2 * J ^ 2) := by
    have hexpand :
        (A * Real.cos φ - C * m / J ^ 2) ^ 2 =
          A ^ 2 * Real.cos φ ^ 2 - 2 * A * Real.cos φ * (C * m / J ^ 2) +
            (C * m / J ^ 2) ^ 2 := by ring
    rw [hexpand]
    -- Collect J²/(2m) A² sin² + J²/(2m) A² cos² = J²/(2m) A²
    have hA :
        J ^ 2 / (2 * m) * (A ^ 2 * Real.sin φ ^ 2) +
            J ^ 2 / (2 * m) * (A ^ 2 * Real.cos φ ^ 2) =
          J ^ 2 / (2 * m) * A ^ 2 := by
      have := congrArg (fun x => J ^ 2 / (2 * m) * A ^ 2 * x) htrig
      ring_nf at this ⊢
      linarith
    -- Remaining cross and constant terms cancel to -C² m /(2 J²)
    have hrest :
        J ^ 2 / (2 * m) * (-(2 * A * Real.cos φ * (C * m / J ^ 2)) + (C * m / J ^ 2) ^ 2) +
            C * (A * Real.cos φ - C * m / J ^ 2) =
          -C ^ 2 * m / (2 * J ^ 2) := by
      field_simp [hm, hm2, hJ2]
      ring
    -- Assemble
    calc
      J ^ 2 / (2 * m) * (A ^ 2 * Real.sin φ ^ 2) +
            J ^ 2 / (2 * m) *
              (A ^ 2 * Real.cos φ ^ 2 - 2 * A * Real.cos φ * (C * m / J ^ 2) +
                (C * m / J ^ 2) ^ 2) +
              C * (A * Real.cos φ - C * m / J ^ 2)
        = (J ^ 2 / (2 * m) * (A ^ 2 * Real.sin φ ^ 2) +
              J ^ 2 / (2 * m) * (A ^ 2 * Real.cos φ ^ 2)) +
            (J ^ 2 / (2 * m) *
                (-(2 * A * Real.cos φ * (C * m / J ^ 2)) + (C * m / J ^ 2) ^ 2) +
              C * (A * Real.cos φ - C * m / J ^ 2)) := by ring
      _ = J ^ 2 / (2 * m) * A ^ 2 + (-C ^ 2 * m / (2 * J ^ 2)) := by
            rw [hA, hrest]
      _ = J ^ 2 / (2 * m) * A ^ 2 - C ^ 2 * m / (2 * J ^ 2) := by ring
  -- Connect mechanical_energy_of_angle to the core expression
  have h1 :
      J ^ 2 / (2 * m * (r φ) ^ 4) * (deriv r φ) ^ 2 =
        J ^ 2 / (2 * m) * (A ^ 2 * Real.sin φ ^ 2) := by
    calc
      J ^ 2 / (2 * m * (r φ) ^ 4) * (deriv r φ) ^ 2
        = J ^ 2 / (2 * m) * ((deriv r φ) ^ 2 / (r φ) ^ 4) := by
            field_simp [hm2, hr4]; try ring
      _ = J ^ 2 / (2 * m) * (A ^ 2 * Real.sin φ ^ 2) := by rw [hsin]
  have h2 :
      J ^ 2 / (2 * m * (r φ) ^ 2) + C / r φ =
        J ^ 2 / (2 * m) * ((r φ)⁻¹) ^ 2 + C * (r φ)⁻¹ := by
    field_simp [hm2, hr2]
    try ring
  simp only [mechanical_energy_of_angle]
  rw [h1, add_assoc, h2, hw]
  convert hcore using 1
  ring


-- created on 2026-09-29
