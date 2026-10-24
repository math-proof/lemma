/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Integral/CarlemanStieltjesCriterion.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Probability.Moments.Basic

import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

/-!
# Carleman's criterion for the Stieltjes moment problem

This file proves that a probability measure on the nonnegative half-line is determined by its
moments when its Stieltjes Carleman series diverges. It also supplies the real-variable
quasi-analytic uniqueness result used in the proof.
-/

set_option autoImplicit false

namespace MetaMathlibExt

open Filter MeasureTheory Set
open scoped BigOperators Topology

private noncomputable def carlemanNormalizedDeriv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) (M : ℕ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ‖iteratedDeriv n f x‖ / ((Real.exp 1) ^ n * M n)

private noncomputable def carlemanBangFunction {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) (M : ℕ → ℝ) (x : ℝ) : ℝ :=
  sSup (Set.range fun n => carlemanNormalizedDeriv f M n x)

private noncomputable def carlemanSymmetrization (σ : Measure ℝ) : Measure ℝ :=
  σ.map Real.sqrt + σ.map fun x => -Real.sqrt x

private noncomputable def carlemanMomentMajorant (ρ : Measure ℝ) (n : ℕ) : ℝ :=
  if Even n then ∫ x, |x| ^ n ∂ρ else
    Real.sqrt ((∫ x, |x| ^ (n - 1) ∂ρ) * ∫ x, |x| ^ (n + 1) ∂ρ)

/-- Stieltjes moment determinacy on the closed nonnegative half-line.
    Corpus `jis_grounded_5e39d97b31ef58deb38a5a58`. Authoritative source:
    Gwo Dong Lin, "Recent Developments on the Moment Problem", Journal of
    Statistical Distributions and Applications (2017), DOI
    10.1186/s40488-017-0059-2, arXiv:1703.01027v3, frozen TeX SHA-256
    e2dcb54a4b25d57ae3ad6e52267862aeca0ae2f38ffb729df0d727013d3c3080,
    definition lines 57-75, criterion lines 297-321. JIS application, frozen
    source SHA-256 66f0a4a264af03f82a43e3b37e62cc80cf0aed6f43e476e56456006203232bd0,
    lines 152-177. Says a probability measure supported on [0, infinity),
    represented by zero mass on `Set.Iio 0`, is uniquely determined among
    probability measures supported there with finite absolute moments by
    equality of every positive moment. -/
def StieltjesMomentDeterminate (μ : MeasureTheory.Measure ℝ) : Prop :=
  ∀ (ν : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure ν],
    ν (Set.Iio (0 : ℝ)) = 0 →
    (∀ k : ℕ, 0 < k → MeasureTheory.Integrable (fun x : ℝ => |x| ^ k) ν) →
    (∀ k : ℕ, 0 < k →
      ProbabilityTheory.moment (id : ℝ → ℝ) k ν =
        ProbabilityTheory.moment (id : ℝ → ℝ) k μ) →
    ν = μ
end MetaMathlibExt
