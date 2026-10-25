/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Topology.Connected.TotallyDisconnected
import Def.Probability.LevyKhintchin.Part17
open MeasureTheory
open scoped ENNReal NNReal MeasureTheory Topology

/-!
# The Lévy–Khintchin representation

This file proves the one-dimensional Lévy–Khintchin characterization of infinitely divisible
probability measures, with the hard truncation convention at radius one.
-/


namespace MetaMathlibExt

lemma lk_canonical_triplet {L : ℝ → ℂ} (K : FiniteMeasure ℝ) (b : ℝ)
    (hL : ∀ t : ℝ, L t = Complex.I * (t : ℂ) * (b : ℂ) +
      ∫ x, lkCanonicalIntegrand t x ∂(K : Measure ℝ)) :
    ∃ gamma : ℝ, ∃ sigma : ℝ, 0 ≤ sigma ∧
      ∃ nu : Measure ℝ, nu {0} = 0 ∧
        (∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂nu < ∞) ∧
          ∀ t : ℝ, L t = lkExponent gamma sigma nu t := by
  let nu := lkLevyMeasure K
  let c : ℝ := ∫ x, lkDriftCorrection x ∂nu
  let gamma := b + c
  let sigma := lkGaussianCoefficient K
  have hnu : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂nu < ∞ :=
    lk_levyMeasure_moment K
  refine ⟨gamma, sigma, lk_gaussianCoefficient_nonneg K, nu,
    lk_levyMeasure_zero K, hnu, fun t ↦ ?_⟩
  rw [hL t, lk_integral_canonical_eq_atom_add_smooth,
    lk_integral_smoothJump_eq_jump_add_correction hnu,
    ← lk_gaussianCoefficient_sq K]
  unfold lkExponent gamma c sigma
  push_cast
  ring

lemma lk_exists_root_sequence {mu : Measure ℝ} [IsProbabilityMeasure mu]
    (hID : ∀ n : ℕ, n ≠ 0 →
      ∃ rho : Measure ℝ, IsProbabilityMeasure rho ∧
        mu = Nat.iterate (Measure.conv rho) (n - 1) rho)
    {L : ℝ → ℂ} (hL : Continuous L) (hL0 : L 0 = 0)
    (hLexp : ∀ t : ℝ, Complex.exp (L t) = charFun mu t) :
    ∃ rho : ℕ → Measure ℝ, (∀ n, IsProbabilityMeasure (rho n)) ∧
      ∀ n t, charFun (rho n) t =
        Complex.exp (L t / ((n + 1 : ℕ) : ℝ)) := by
  choose rho hprob hroot using fun n ↦
    lk_exists_exp_root hID hL hL0 hLexp (Nat.succ_ne_zero n)
  exact ⟨rho, hprob, hroot⟩

lemma lk_triplet_of_infinitelyDivisible {mu : Measure ℝ}
    [IsProbabilityMeasure mu]
    (hID : ∀ n : ℕ, n ≠ 0 →
      ∃ rho : Measure ℝ, IsProbabilityMeasure rho ∧
        mu = Nat.iterate (Measure.conv rho) (n - 1) rho) :
    ∃ gamma : ℝ, ∃ sigma : ℝ, 0 ≤ sigma ∧
      ∃ nu : Measure ℝ, nu {0} = 0 ∧
        (∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂nu < ∞) ∧
          ∀ t : ℝ, charFun mu t = Complex.exp (lkExponent gamma sigma nu t) := by
  obtain ⟨L, hL, hL0, hLexp⟩ := lk_exists_distinguishedLog hID
  obtain ⟨rho, hprob, hroot⟩ := lk_exists_root_sequence hID hL hL0 hLexp
  obtain ⟨K, U, hU, hK⟩ := lk_exists_canonical_limit hprob hL hL0 hroot
  obtain ⟨b, hrep⟩ := lk_log_eq_drift_add_canonical hprob hroot hU hK
  obtain ⟨gamma, sigma, hsigma, nu, hnu0, hnu, htrip⟩ :=
    lk_canonical_triplet K b hrep
  refine ⟨gamma, sigma, hsigma, nu, hnu0, hnu, fun t ↦ ?_⟩
  rw [← hLexp t, htrip t]

/-- Lévy–Khintchin representation: a law `μ` on `ℝ` is infinitely divisible
iff its characteristic function has the drift–Gaussian–jump form with a drift
`γ`, a Gaussian coefficient `σ ≥ 0`, and a Lévy measure `ν` with `ν {0} = 0`
and `∫⁻ x, min 1 (x ^ 2) ∂ν < ∞`.
Source: Ken-iti Sato, *Lévy Processes and Infinitely Divisible Distributions*,
Cambridge Studies in Advanced Mathematics 68, Cambridge University Press (1999),
Theorem 8.1, pp. 37–38, ISBN 978-0-521-55302-5.
<https://books.google.com/books?vid=ISBN9780521553025&jscmd=SearchWithinVolume2&q=Theorem+8.1>
Scope: restricts Sato Theorem 8.1 (stated for `ℝ^d`) to `ℝ`, and formalizes
only the existence direction (i), omitting uniqueness of the generating
triplet (ii). The jump integrand uses the hard truncation `x * 1_{|x| ≤ 1}`,
which is an equivalent convention to Sato's `x / (1 + |x|^2)` after
reparameterizing the drift `γ`.

Proves `Wanted` entry `levy_Khintchin`.

Proof: The reverse implication uses compound Poisson approximation plus Lévy continuity; the
forward implication uses a distinguished logarithm, canonical measures, and Prokhorov compactness.
For the equivalence, see William Feller, *An Introduction to Probability Theory and Its
Applications*, vol. II, Theorem XVII.2.1.
-/
theorem levy_Khintchin :
    ∀ (μ : MeasureTheory.Measure ℝ), MeasureTheory.IsProbabilityMeasure μ →
      ((∀ n : ℕ, n ≠ 0 →
          ∃ ν : MeasureTheory.Measure ℝ, MeasureTheory.IsProbabilityMeasure ν ∧
            μ = Nat.iterate (MeasureTheory.Measure.conv ν) (n - 1) ν) ↔
        ∃ γ : ℝ, ∃ σ : ℝ, 0 ≤ σ ∧
          ∃ ν : MeasureTheory.Measure ℝ,
            ν {0} = 0 ∧ (∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν < ∞) ∧
              ∀ t : ℝ, MeasureTheory.charFun μ t =
                Complex.exp ((Complex.I * (γ : ℂ) * (t : ℂ) -
                  (((σ ^ 2 * t ^ 2 : ℝ) : ℂ) / 2) +
                  ∫ x, (Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) - 1 -
                    Set.indicator {y : ℝ | |y| ≤ 1}
                      (fun y => Complex.I * (t : ℂ) * (y : ℂ)) x) ∂ν))) := by
  intro mu hmu
  constructor
  · intro hID
    obtain ⟨gamma, sigma, hsigma, nu, hnu0, hnu, hchar⟩ :=
      lk_triplet_of_infinitelyDivisible hID
    refine ⟨gamma, sigma, hsigma, nu, hnu0, hnu, fun t ↦ ?_⟩
    rw [hchar t]
    rfl
  · rintro ⟨gamma, sigma, -, nu, -, hnu, hchar⟩
    apply lk_infinitelyDivisible_of_charFun hmu hnu gamma sigma
    intro t
    rw [hchar t]
    rfl

end MetaMathlibExt
