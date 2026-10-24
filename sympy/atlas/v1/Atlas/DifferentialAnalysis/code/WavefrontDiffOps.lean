/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontDiffOps.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.WavefrontSet
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.WavefrontSet
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.ConeSupportCorollary
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.WavefrontCharacterization
import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.ConeSupportCorollary
import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.WavefrontCharacterization

noncomputable section

open scoped SchwartzMap FourierTransform
open MeasureTheory ConeSupport

namespace WavefrontDiffOps

variable {n : ℕ}

/-- The "boundary" subset of pairs `(p, q)` where at least one of the components corresponds to
a direction at infinity (an `Sum.inr` of `Sphere n`). -/
def boundaryOfProd : Set ((E n ⊕ Sphere n) × (E n ⊕ Sphere n)) :=
  {p | (∃ ω : Sphere n, p.1 = Sum.inr ω) ∨ (∃ ω : Sphere n, p.2 = Sum.inr ω)}
