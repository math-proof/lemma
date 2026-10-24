/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSetCorollaries.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.WavefrontSet
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.WavefrontSet
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.ConeSupportCorollary
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.PseudoDiffOps
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.WavefrontCharacterization
import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.ConeSupportCorollary
import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.PseudoDiffOps
import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.WavefrontCharacterization
import Mathlib.Algebra.Group.Pointwise.Set.Basic

noncomputable section

open scoped SchwartzMap FourierTransform Pointwise
open MeasureTheory

namespace ConeSupport

variable {n : ℕ}

/-- Two tempered distributions `u`, `v` admit an extended convolution as soon as at least one of
them has empty conic singular support on the sphere; this is the side condition under which
the convolution `u * v` can be defined microlocally. -/
def HasExtendedConvolution (u v : 𝓢'(E n, ℂ)) : Prop :=
  ConicSingularSupportSphere u = ∅ ∨ ConicSingularSupportSphere v = ∅

/-- The extended convolution `u * v` defined under `HasExtendedConvolution u v` by splitting
the distribution with empty conic singular support into a Schwartz part and a compactly
supported part. -/
def extConv (u v : 𝓢'(E n, ℂ)) (h : HasExtendedConvolution u v) : 𝓢'(E n, ℂ) :=
  if hu : ConicSingularSupportSphere u = ∅ then
    let hecs := hasEmptyConicSingularSupportSphere_of_eq_empty u hu
    let d := hecs.hasDecomp.some
    let cs := standardConvolutionSystem v
    cs.convSchwartz d.schwartzPart + cs.convCompact d.compactPart
  else
    let hv : ConicSingularSupportSphere v = ∅ := h.resolve_left hu
    let hecs := hasEmptyConicSingularSupportSphere_of_eq_empty v hv
    let d := hecs.hasDecomp.some
    let cs := standardConvolutionSystem u
    cs.convSchwartz d.schwartzPart + cs.convCompact d.compactPart
