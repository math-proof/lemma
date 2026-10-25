/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ConvolutionTheorem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.DifferentialAnalysis.code.DifferentialOperators.Part2
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.DifferentialOperators
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SchwartzTranslation
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.HormanderFundamental
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.DistributionSupport
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SobolevDerivatives
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SobolevEmbedding
import Theorem.v1.Atlas.DifferentialAnalysis.code.SchwartzTranslation
import Def.v1.Atlas.DifferentialAnalysis.code.HormanderFundamental
import Theorem.v1.Atlas.DifferentialAnalysis.code.DistributionSupport
import Def.v1.Atlas.DifferentialAnalysis.code.SobolevDerivatives
import Def.v1.Atlas.DifferentialAnalysis.code.SobolevEmbedding.Part5
open scoped SchwartzMap LineDeriv Pointwise
open TemperedDistribution SchwartzMap DifferentialOperators Distribution
     SobolevSpace SchwartzRepresentation


noncomputable section

namespace DifferentialOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The convolution of a tempered distribution `u` with a Schwartz function `φ`, viewed
as a function `x ↦ ⟨u, φ(· - x)⟩` on `E`. -/
noncomputable def tempDistSchwartzConv
    (u : 𝓢'(E, ℂ)) (φ : 𝓢(E, ℂ)) : E → ℂ :=
  fun x => u (compSubConstCLM ℂ x φ)

end DifferentialOperators
end
