/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Def.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM14.WaveEnergy.Part2
open MeasureTheory Set Finset Classical


public noncomputable section

namespace CM14

/-- A spacetime domain $\Omega$ is regular if it is open, bounded and has compact closure;
the hypotheses needed to state the divergence theorem cleanly. -/
structure IsRegularDomain {n : ℕ} (Ω : Set (WaveSpacetime n)) : Prop where
  isOpen : IsOpen Ω
  isBounded : Bornology.IsBounded Ω
  isCompact_closure : IsCompact (closure Ω)

end CM14
end
