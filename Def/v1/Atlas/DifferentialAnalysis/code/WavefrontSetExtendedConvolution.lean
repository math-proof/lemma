/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSetExtendedConvolution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.DifferentialAnalysis.code.WavefrontSet.Part3
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.WavefrontSet


noncomputable section

open scoped SchwartzMap FourierTransform

open MeasureTheory Set

namespace ConeSupport

variable {n : ℕ}

/-- The extended convolution `u ⋆ v` of tempered distributions, defined when the left
factor `u` has empty conic singular support sphere by decomposing `u` into a Schwartz part
and a compactly supported part and convolving each with `v` (Melrose, Section 12). -/
def extendedConvolution
    (u v : 𝓢'(E n, ℂ))
    (hu : ConicSingularSupportSphere u = ∅) :
    𝓢'(E n, ℂ) :=
  let hempty := hasEmptyConicSingularSupportSphere_of_eq_empty u hu
  let d := hempty.hasDecomp.some
  (standardConvolutionSystem v).convSchwartz d.schwartzPart +
    (standardConvolutionSystem v).convCompact d.compactPart

/-- The extended convolution `u ⋆ v` of tempered distributions, defined when the right
factor `v` has empty conic singular support sphere by decomposing `v` into a Schwartz part
and a compactly supported part and convolving each with `u`. -/
def extendedConvolutionRight
    (u v : 𝓢'(E n, ℂ))
    (hv : ConicSingularSupportSphere v = ∅) :
    𝓢'(E n, ℂ) :=
  let hempty := hasEmptyConicSingularSupportSphere_of_eq_empty v hv
  let d := hempty.hasDecomp.some
  (standardConvolutionSystem u).convSchwartz d.schwartzPart +
    (standardConvolutionSystem u).convCompact d.compactPart

end ConeSupport
end
