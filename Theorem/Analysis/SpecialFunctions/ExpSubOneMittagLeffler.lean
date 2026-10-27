/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic
/-!
# Mittag-Leffler expansion of the Bose-Einstein kernel
-/


namespace MetaMathlibExt

open scoped BigOperators

open Complex

noncomputable section

/-- The Mittag-Leffler expansion of the Bose-Einstein kernel on the real line. -/
theorem one_div_exp_sub_one_eq_tsum (u : ℝ) (hu : u ≠ 0) :
    1 / (Real.exp u - 1) = 1 / u - 1 / 2 +
      ∑' m : ℕ, 2 * u / (u ^ 2 + 4 * Real.pi ^ 2 * (m + 1 : ℕ) ^ 2) := by
  let z : ℂ := Complex.I * (u : ℂ) / (2 * (Real.pi : ℂ))
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hz_im : z.im = u / (2 * Real.pi) := by
    dsimp [z]
    simp [Complex.div_im]
    field_simp [Real.pi_ne_zero]
  have hz : z ∈ Complex.integerComplement := by
    rw [Complex.mem_integerComplement_iff]
    rintro ⟨k, hk⟩
    have him := congr_arg Complex.im hk
    rw [hz_im] at him
    norm_num at him
    rcases div_eq_zero_iff.mp him.symm with hu0 | hpi0
    · exact hu hu0
    · exact Real.pi_ne_zero ((mul_eq_zero.mp hpi0).resolve_left (by norm_num))
  have hexp : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z) =
      (Real.exp (-u) : ℝ) := by
    rw [Complex.ofReal_exp]
    congr 1
    dsimp [z]
    field_simp [hpi]
    ring_nf
    simp
  have hq : Real.exp (-u) ≠ 1 := by
    simpa [Real.exp_eq_one_iff] using hu
  have hscaled := congr_arg (fun w : ℂ => Complex.I / (2 * (Real.pi : ℂ)) * w)
    (cot_series_rep' hz)
  rw [← tsum_mul_left] at hscaled
  have hleft :
      Complex.I / (2 * (Real.pi : ℂ)) *
          ((Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * z) - 1 / z) =
        ((1 / (Real.exp u - 1) + 1 / 2 - 1 / u : ℝ) : ℂ) := by
    rw [Complex.cot_pi_eq_exp_ratio, hexp]
    rw [Real.exp_neg]
    push_cast
    have heu : Real.exp u ≠ 0 := Real.exp_ne_zero u
    rw [← Complex.ofReal_exp]
    have hdenR : (1 : ℝ) - (Real.exp u)⁻¹ ≠ 0 := by
      rw [sub_ne_zero]
      intro he
      apply hq
      rw [Real.exp_neg, he]
    have hden : (1 : ℂ) - (Real.exp u : ℂ)⁻¹ ≠ 0 := by
      exact_mod_cast hdenR
    have hEuR : Real.exp u - 1 ≠ 0 := by
      rw [sub_ne_zero]
      exact (Real.exp_eq_one_iff u).not.mpr hu
    have hEu : (Real.exp u : ℂ) - 1 ≠ 0 := by
      exact_mod_cast hEuR
    dsimp [z]
    field_simp [hpi, Complex.I_ne_zero, Complex.I_mul_I, hu, heu, hden, hEu]
    ring
  have hterm : ∀ m : ℕ,
      Complex.I / (2 * (Real.pi : ℂ)) *
          (1 / (z - ((m : ℂ) + 1)) + 1 / (z + ((m : ℂ) + 1))) =
        ((2 * u / (u ^ 2 + 4 * Real.pi ^ 2 * (m + 1 : ℕ) ^ 2) : ℝ) : ℂ) := by
    intro m
    have hmden : (u : ℂ) ^ 2 + 4 * (Real.pi : ℂ) ^ 2 * ((m + 1 : ℕ) : ℂ) ^ 2 ≠ 0 := by
      have heq : (u : ℂ) ^ 2 + 4 * (Real.pi : ℂ) ^ 2 * ((m + 1 : ℕ) : ℂ) ^ 2 =
          ((u ^ 2 + 4 * Real.pi ^ 2 * (m + 1 : ℕ) ^ 2 : ℝ) : ℂ) := by
        push_cast
        ring
      rw [heq]
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity))
    have hminus : z - ((m : ℂ) + 1) ≠ 0 := by
      simpa [sub_eq_add_neg] using
        (Complex.integerComplement_add_ne_zero hz (-((m : ℤ) + 1)))
    have hplus : z + ((m : ℂ) + 1) ≠ 0 := by
      simpa using (Complex.integerComplement_add_ne_zero hz ((m : ℤ) + 1))
    field_simp [hpi, hmden, hminus, hplus]
    dsimp [z]
    push_cast
    field_simp [hpi, Complex.I_mul_I]
    have hmden' : (u : ℂ) ^ 2 + (Real.pi : ℂ) ^ 2 * ((m : ℂ) + 1) ^ 2 * 4 ≠ 0 := by
      convert hmden using 1
      push_cast
      ring
    rw [eq_div_iff hmden']
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [hleft] at hscaled
  simp_rw [hterm] at hscaled
  rw [← Complex.ofReal_tsum] at hscaled
  have hr := Complex.ofReal_inj.mp hscaled
  linarith

end
end MetaMathlibExt
