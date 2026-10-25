/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter11/AdvancedResults.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Distribution.FourierMultiplier
import Abbrev.v1.Atlas.HighDimensionalStatistics.code.Chapter11.Defs_and_Props.Part3
import Abbrev.v1.Atlas.HighDimensionalStatistics.code.Chapter11.AdvancedResults.Part3
set_option maxHeartbeats 800000


noncomputable section

open scoped SchwartzMap FourierTransform Laplacian BigOperators Pointwise

open MeasureTheory TemperedDistribution Filter ContinuousLinearMap

namespace Chapter11

variable {n : ℕ}

section Prop_11_15_SingSuppConvolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasureSpace E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E] [(MeasureTheory.volume : Measure E).HasTemperateGrowth]

/-- A tempered distribution has compact support if it is annihilated by every
Schwartz function vanishing on some fixed compact set. -/
def HasCompactDistribSupport (u : 𝓢'(E, ℂ)) : Prop :=
  ∃ K : Set E, IsCompact K ∧
    ∀ φ : 𝓢(E, ℂ), (∀ x ∈ K, φ x = 0) → u φ = 0

/-- Convolution `u * f` of a compactly-supported tempered distribution `u` with
another tempered distribution `f`. -/

end Prop_11_15_SingSuppConvolution

section Prop_11_16_HeatEquation

/-- The last coordinate of a point of `ℝⁿ⁺¹` (interpreted as the time variable
for the heat equation). -/
def lastCoord (n : ℕ) (x : Rn (n + 1)) : ℝ :=
  (WithLp.equiv 2 (Fin (n + 1) → ℝ) x) (Fin.last n)

/-- The unit vector pointing in the time direction (the last coordinate) of
`ℝⁿ⁺¹`. -/
def timeDir (n : ℕ) : Rn (n + 1) := EuclideanSpace.single (Fin.last n) 1

/-- The `i`-th spatial direction in `ℝⁿ⁺¹` (the first `n` coordinates). -/
def spatialDir (n : ℕ) (i : Fin n) : Rn (n + 1) :=
  EuclideanSpace.single (Fin.castSucc i) 1

/-- The time-derivative operator `∂_t` on tempered distributions over `ℝⁿ⁺¹`. -/
def timeDerivCLM (n : ℕ) : 𝓢'(Rn (n + 1), ℂ) →L[ℂ] 𝓢'(Rn (n + 1), ℂ) :=
  LineDeriv.lineDerivOpCLM ℂ 𝓢'(Rn (n + 1), ℂ) (timeDir n)

/-- The second-order spatial derivative `∂_i²` on tempered distributions. -/
def spatialSecondDerivCLM (n : ℕ) (i : Fin n) :
    𝓢'(Rn (n + 1), ℂ) →L[ℂ] 𝓢'(Rn (n + 1), ℂ) :=
  (LineDeriv.lineDerivOpCLM ℂ 𝓢'(Rn (n + 1), ℂ) (spatialDir n i)).comp
    (LineDeriv.lineDerivOpCLM ℂ 𝓢'(Rn (n + 1), ℂ) (spatialDir n i))

/-- The spatial Laplacian `Δ = ∑_i ∂_i²` acting in the first `n` coordinates. -/
def spatialLaplacianCLM (n : ℕ) : 𝓢'(Rn (n + 1), ℂ) →L[ℂ] 𝓢'(Rn (n + 1), ℂ) :=
  ∑ i : Fin n, spatialSecondDerivCLM n i

/-- The heat operator `∂_t + Δ_x` on tempered distributions over `ℝⁿ⁺¹`. -/
def heatOp (n : ℕ) : 𝓢'(Rn (n + 1), ℂ) →L[ℂ] 𝓢'(Rn (n + 1), ℂ) :=
  timeDerivCLM n + spatialLaplacianCLM n

/-- A tempered distribution has support in the future half-space `{t ≤ -T}` if it
is annihilated by every Schwartz function vanishing there. -/
def HasSupportInFutureHalfSpace (n : ℕ) (T : ℝ) (u : 𝓢'(Rn (n + 1), ℂ)) : Prop :=
  ∀ φ : 𝓢(Rn (n + 1), ℂ),
    (∀ x : Rn (n + 1), lastCoord n x ≥ -T → φ x = 0) → u φ = 0

end Prop_11_16_HeatEquation

/-- The principal symbol operator associated with a polynomial `P` of order `m`,
realised as the Fourier multiplier with symbol the degree-`m` homogeneous component
of `P`. -/
def principalSymbolOp {n : ℕ} (P : MvPolynomial (Fin n) ℂ) (m : ℕ) :
    𝓢'(Rn n, ℂ) →L[ℂ] 𝓢'(Rn n, ℂ) :=
  TemperedDistribution.fourierMultiplierCLM ℂ
    (fun ξ => evalPolyAtRn n (MvPolynomial.homogeneousComponent m P) ξ)

end Chapter11
end
