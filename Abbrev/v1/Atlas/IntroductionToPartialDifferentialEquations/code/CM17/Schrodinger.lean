/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM17/Schrodinger.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM16.FourierTransform
import Lemma.Real.Atlas.v1.IntroductionToPartialDifferentialEquations.code.CM16.FourierTransform
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Distribution.FourierMultiplier
open MeasureTheory Complex FourierTransform


noncomputable section

namespace SchrodingerEquation

/-- Abbreviation for the $n$-dimensional Euclidean space $\mathbb{R}^n$. -/
abbrev Rn (n : ℕ) := EuclideanSpace ℝ (Fin n)

end SchrodingerEquation
end
