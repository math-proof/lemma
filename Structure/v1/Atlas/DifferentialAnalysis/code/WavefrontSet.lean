/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Distribution.Support
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Fourier.Convolution
import Def.v1.Atlas.DifferentialAnalysis.code.DifferentialOperators.Part2
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.DifferentialOperators
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.HormanderFundamental
import Def.v1.Atlas.DifferentialAnalysis.code.HormanderFundamental
import Abbrev.v1.Atlas.DifferentialAnalysis.code.WavefrontSet.Part2


noncomputable section

open scoped SchwartzMap FourierTransform

open MeasureTheory Set

namespace ConeSupport

variable {n : ℕ}

/-- A decomposition of a tempered distribution `u` into a Schwartz part and a
compactly supported part. -/
structure SchwartzCompactDecomp (u : 𝓢'(E n, ℂ)) where
  schwartzPart : 𝓢(E n, ℂ)
  compactPart : 𝓢'(E n, ℂ)
  compactPart_isCompactlySupported : IsCompactlySupportedDistribution compactPart
  sum_eq : u = schwEmbed schwartzPart + compactPart

/-- Predicate stating that `u` admits at least one `SchwartzCompactDecomp`,
and any two such decompositions differ by a compactly supported distribution. -/
structure HasEmptyConicSingularSupportSphere (u : 𝓢'(E n, ℂ)) : Prop where
  hasDecomp : Nonempty (SchwartzCompactDecomp u)
  diff_compactlySupported : ∀ (d₁ d₂ : SchwartzCompactDecomp u),
    IsCompactlySupportedDistribution (schwEmbed d₁.schwartzPart - schwEmbed d₂.schwartzPart)

/-- Abstract data for performing convolutions of tempered distributions: a
"Schwartz-against" operator that is additive, a "compact-against" operator
that is additive, and a compatibility condition saying the two agree when the
input is compactly supported. -/
structure ConvolutionSystem (n : ℕ) where
  convSchwartz : 𝓢(E n, ℂ) → 𝓢'(E n, ℂ)
  convCompact : 𝓢'(E n, ℂ) → 𝓢'(E n, ℂ)
  convSchwartz_add : ∀ φ₁ φ₂, convSchwartz (φ₁ + φ₂) = convSchwartz φ₁ + convSchwartz φ₂
  convCompact_add : ∀ u₁ u₂, convCompact (u₁ + u₂) = convCompact u₁ + convCompact u₂
  convSchwartz_eq_compact : ∀ φ : 𝓢(E n, ℂ),
    IsCompactlySupportedDistribution (schwEmbed φ) →
    convSchwartz φ = convCompact (schwEmbed φ)


end ConeSupport
end
