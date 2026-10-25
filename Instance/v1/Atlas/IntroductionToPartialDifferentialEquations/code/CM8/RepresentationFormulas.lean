/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM8/RepresentationFormulas.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Topology.Algebra.Support
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Structure.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM8.GreenFunctions.Part2
import Lemma.Real.Atlas.v1.IntroductionToPartialDifferentialEquations.code.CM8.GreenFunctions
import Structure.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM8.RepresentationFormulas
open Real Set MeasureTheory


noncomputable section

namespace CM8

/-- Instance: $2 \le 3$, supplied so that `FundSolN` and related results specialise to the
three-dimensional setting. -/
instance : Fact (2 ≤ 3) := ⟨by omega⟩

end CM8
end
