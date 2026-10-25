/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Def.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM14.WaveEnergy.Part2
open MeasureTheory Set Finset Classical


noncomputable section

namespace CM14

/-- A spacetime domain $\Omega$ is regular if it is open, bounded and has compact closure;
the hypotheses needed to state the divergence theorem cleanly. -/
structure IsRegularDomain {n : ℕ} (Ω : Set (WaveSpacetime n)) : Prop where
  isOpen : IsOpen Ω
  isBounded : Bornology.IsBounded Ω
  isCompact_closure : IsCompact (closure Ω)

end CM14
end
