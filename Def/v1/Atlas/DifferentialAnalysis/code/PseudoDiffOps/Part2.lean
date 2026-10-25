/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/PseudoDiffOps.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.DifferentialAnalysis.code.DifferentialOperators.Part2
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.DifferentialOperators
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.ConvolutionTheorem
import Def.v1.Atlas.DifferentialAnalysis.code.ConvolutionTheorem
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.Compactness.LocallyCompact
import Theorem.v1.Atlas.DifferentialAnalysis.code.PseudoDiffOps


noncomputable section

open scoped SchwartzMap Pointwise

open MeasureTheory Set Function TemperedDistribution

namespace DifferentialOperators

variable {n : ℕ}

/-- The reflection `φ ↦ φ ∘ (-id)` as a continuous linear endomorphism of the Schwartz
space `𝓢(EuclideanSpace ℝ (Fin n), ℂ)`. -/
def schwNegReflCLM :
    𝓢(EuclideanSpace ℝ (Fin n), ℂ) →L[ℂ] 𝓢(EuclideanSpace ℝ (Fin n), ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ)

/-- Cross-correlation with a compactly supported distribution `μ`, viewed as a continuous
linear endomorphism of `𝓢(EuclideanSpace ℝ (Fin n), ℂ)`. -/
def crossCorrSchwartzCLM
    (μ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hμ : HasCompactSupport μ) :
    𝓢(EuclideanSpace ℝ (Fin n), ℂ) →L[ℂ] 𝓢(EuclideanSpace ℝ (Fin n), ℂ) :=
  let hμ' := hasCompactDsupport_of_hasCompactSupport μ hμ
  { toLinearMap :=
      { toFun := compactDsupportConvolutionSchwartzMap μ hμ'
        map_add' := compactDsupportConvolution_map_add μ hμ'
        map_smul' := compactDsupportConvolution_map_smul μ hμ' }
    cont := continuous_compactDsupportConvolution μ hμ' }

/-- Convolution with a compactly supported distribution `μ` on Schwartz functions, given
as the reflection composed with cross-correlation. -/
def convolutionSchwartzCLM
    (μ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hμ : HasCompactSupport μ) :
    𝓢(EuclideanSpace ℝ (Fin n), ℂ) →L[ℂ] 𝓢(EuclideanSpace ℝ (Fin n), ℂ) :=
  schwNegReflCLM.comp (crossCorrSchwartzCLM μ hμ)

/-- The convolution `μ * f` of two tempered distributions, defined when the left factor
`μ` has compact support, by precomposing `f` with convolution by `μ` on Schwartz test
functions. -/
def distribConvolution
    (μ f : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hμ : HasCompactSupport μ) :
    𝓢'(EuclideanSpace ℝ (Fin n), ℂ) :=
  (PointwiseConvergenceCLM.precomp ℂ (convolutionSchwartzCLM μ hμ)) f

end DifferentialOperators
end
