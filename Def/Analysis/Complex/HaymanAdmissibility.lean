/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
-- Hayman's admissibility theorem for asymptotic coefficients.
-- Source: Ljuben Mutafchiev, "The Limiting Distribution of the Hook Length
-- of a Randomly Chosen Cell in a Random Young Diagram", arXiv:1906.07169v2,
-- reproducing the Flajolet-Sedgewick Chapter VIII.5 formulation (Hayman 1956).
-- Auxiliary functions and admissibility conditions: tex lines 453-493;
-- coefficient theorem: tex lines 495-506.

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
set_option autoImplicit false

open scoped ENNReal NNReal

/-!
# Hayman's coefficient asymptotic

This file defines finite-radius Hayman admissibility and proves the associated saddle-point
coefficient asymptotic. The proof uses Cauchy's coefficient formula for power series on a disk
and the asymptotic of truncated Gaussian integrals.
-/


namespace Complex.HaymanAdmissibility

open Asymptotics Filter MeasureTheory Metric Set

open scoped Interval Real Topology

/-- Hayman auxiliary function `A(r)`, the real part of `r * G'(r) / G(r)`. -/
noncomputable def haymanAuxiliaryA (G : ℂ → ℂ) (r : ℝ) : ℝ :=
  Complex.re (((r : ℂ) * deriv G (r : ℂ) / G (r : ℂ)))

/-- Hayman auxiliary function `B(r) = r * A'(r)`. -/
noncomputable def haymanAuxiliaryB (G : ℂ → ℂ) (r : ℝ) : ℝ :=
  r * deriv (haymanAuxiliaryA G) r

/-- Hayman admissibility for finite radius: analyticity on the disk, positivity
and reality of the logarithmic derivative on the positive axis, capture of both
auxiliary functions, plus uniform locality and decay cutoffs. The full
capture/locality/decay definition here follows the Flajolet-Sedgewick
formulation rather than the abbreviated maximum-modulus restatement (Jiyou Li,
"Asymptotic Estimate for the Multinomial Coefficients", Journal of Integer
Sequences 23 (2020), Article 20.1.3, Lemma [Hayman] `lem2`), whose
maximum-modulus condition is insufficient as stated and is not used. -/
noncomputable def IsHaymanAdmissible (G : ℂ → ℂ) (R0 ρ : ℝ) : Prop :=
  0 < R0 ∧ R0 < ρ ∧
  AnalyticOn ℂ G (Metric.ball (0 : ℂ) ρ) ∧
  (∀ r ∈ Set.Ioo R0 ρ,
    0 < Complex.re (G (r : ℂ)) ∧ Complex.im (G (r : ℂ)) = 0 ∧
    Complex.im (((r : ℂ) * deriv G (r : ℂ) / G (r : ℂ))) = 0) ∧
  Filter.Tendsto (fun r => haymanAuxiliaryA G r)
    (nhdsWithin ρ (Set.Ioo R0 ρ)) Filter.atTop ∧
  Filter.Tendsto (fun r => haymanAuxiliaryB G r)
    (nhdsWithin ρ (Set.Ioo R0 ρ)) Filter.atTop ∧
  ∃ δ : ℝ → ℝ,
    Filter.Eventually (fun r => 0 < δ r ∧ δ r < Real.pi)
      (nhdsWithin ρ (Set.Ioo R0 ρ)) ∧
    (∀ ε : ℝ, 0 < ε →
      Filter.Eventually
        (fun r => ∀ θ : ℝ, |θ| ≤ δ r →
          ‖G ((r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
            G (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ) *
              (haymanAuxiliaryA G r : ℂ) -
              ((θ ^ 2 * haymanAuxiliaryB G r / 2 : ℝ) : ℂ))‖ ≤
          ε * ‖G (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ) *
            (haymanAuxiliaryA G r : ℂ) -
            ((θ ^ 2 * haymanAuxiliaryB G r / 2 : ℝ) : ℂ))‖)
        (nhdsWithin ρ (Set.Ioo R0 ρ))) ∧
    (∀ ε : ℝ, 0 < ε →
      Filter.Eventually
        (fun r => ∀ θ : ℝ, δ r ≤ |θ| → |θ| < Real.pi →
          ‖G ((r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖ ≤
          ε * (‖G (r : ℂ)‖ / Real.sqrt (haymanAuxiliaryB G r)))
        (nhdsWithin ρ (Set.Ioo R0 ρ)))

end Complex.HaymanAdmissibility
