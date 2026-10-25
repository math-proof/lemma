/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/HeatEquationProp1116.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Distribution.Support
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Def.v1.Atlas.DifferentialAnalysis.code.DifferentialOperators.Part2
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.DifferentialOperators
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SchwartzPartition
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SchwartzCutoffConvergence
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.DistributionSupport
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SmoothingOperators
import Theorem.v1.Atlas.DifferentialAnalysis.code.SchwartzPartition
import Def.v1.Atlas.DifferentialAnalysis.code.SchwartzCutoffConvergence
import Theorem.v1.Atlas.DifferentialAnalysis.code.DistributionSupport
import Def.v1.Atlas.DifferentialAnalysis.code.SmoothingOperators
import Abbrev.v1.Atlas.DifferentialAnalysis.code.HeatEquationProp1116


noncomputable section

open scoped SchwartzMap

open TemperedDistribution LineDeriv Distribution

namespace HeatEquation

variable (n : ℕ)

/-- The unit vector in the time direction (index `0`) in space-time. -/
def timeDirection : SpaceTime n :=
  EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)

/-- The `i`-th spatial unit vector in space-time (at index `i.succ`, since `0` is time). -/
def spatialDirection (i : Fin n) : SpaceTime n :=
  EuclideanSpace.single i.succ (1 : ℝ)

/-- The (positive) spatial Laplacian `Δ_x = Σ ∂²/∂xᵢ²` acting on tempered distributions on
space-time. -/
def positiveSpatialLaplacian (u : 𝓢'(SpaceTime n, ℂ)) : 𝓢'(SpaceTime n, ℂ) :=
  ∑ i : Fin n, ∂_{spatialDirection n i} (∂_{spatialDirection n i} u)

/-- The heat operator `∂_t - Δ_x` acting on tempered distributions on space-time. -/
def heatOperator (u : 𝓢'(SpaceTime n, ℂ)) : 𝓢'(SpaceTime n, ℂ) :=
  ∂_{timeDirection n} u - positiveSpatialLaplacian n u

/-- A tempered distribution has compact distributional support if its `dsupport` is compact. -/
def HasCompactDSupport (u : 𝓢'(SpaceTime n, ℂ)) : Prop :=
  IsCompact (dsupport u)

/-- The time coordinate of a space-time point `x`, i.e. `x 0`. -/
def timeCoord (x : SpaceTime n) : ℝ := x 0

/-- A tempered distribution `u` is supported in `{t ≥ c}` if its distributional support is
contained in the half-space `{x | timeCoord x ≥ c}`. -/
def SupportedInTimeGeq (u : 𝓢'(SpaceTime n, ℂ)) (c : ℝ) : Prop :=
  dsupport u ⊆ {x : SpaceTime n | timeCoord n x ≥ c}

/-- The classical heat-kernel density `(4πt)^(-n/2) · exp(-|x|²/(4t))` for `t > 0`, extended by
`0` for `t ≤ 0`. -/
noncomputable def heatKernelFun (v : SpaceTime n) : ℝ :=
  let t := v (0 : Fin (n + 1))
  if t > 0 then
    (4 * Real.pi * t) ^ (-(n : ℝ) / 2) *
      Real.exp (- ‖fun i : Fin n => v i.succ‖ ^ 2 / (4 * t))
  else 0

/-- The heat-kernel measure on space-time: the Lebesgue measure weighted by the heat-kernel
density. -/
def heatKernelMeasure : MeasureTheory.Measure (SpaceTime n) :=
  MeasureTheory.Measure.withDensity MeasureTheory.volume
    (fun v => ENNReal.ofReal (heatKernelFun n v))


open HeatEquation MeasureTheory in
/-- The Lebesgue integral of the heat-kernel density over the time slab `{0 < t < 1}` is finite. -/
noncomputable def HeatEquation.forwardFundSol (n : ℕ) : 𝓢'(SpaceTime n, ℂ) :=
  (heatKernelMeasure n).toTemperedDistribution


open HeatEquation DifferentialOperators in
/-- The continuous linear map sending a Schwartz function `φ` to the convolution
`v * φ` (smoothed via the compact-distributional-support convolution construction), packaged
as a `𝓢(ℝ^(n+1), ℂ) →L[ℂ] 𝓢(ℝ^(n+1), ℂ)` map. -/
def HeatEquation.reflConvSchwartzMap (n : ℕ)
    (v : 𝓢'(SpaceTime n, ℂ)) (hv : HasCompactDSupport n v) :
    𝓢(SpaceTime n, ℂ) →L[ℂ] 𝓢(SpaceTime n, ℂ) :=
  ⟨{ toFun := compactDsupportConvolutionSchwartzMap v hv
     map_add' := compactDsupportConvolution_map_add v hv
     map_smul' := compactDsupportConvolution_map_smul v hv },
   continuous_compactDsupportConvolution v hv⟩


open HeatEquation in
/-- The distributional convolution `dconv n u v hv = u * v` when `v` has compact distributional
support, defined as the composition of `u` with the reflected-convolution Schwartz map. -/
def HeatEquation.dconv (n : ℕ)
    (u v : 𝓢'(SpaceTime n, ℂ)) (hv : HasCompactDSupport n v) :
    𝓢'(SpaceTime n, ℂ) :=
  u.comp (reflConvSchwartzMap n v hv)

end HeatEquation
end
