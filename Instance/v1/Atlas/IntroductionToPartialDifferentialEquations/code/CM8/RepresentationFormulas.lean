/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM8/RepresentationFormulas.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Tactic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Structure.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM8.GreenFunctions.Part2
public import Theorem.Real.Atlas.v1.IntroductionToPartialDifferentialEquations.code.CM8.GreenFunctions
public import Structure.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM8.RepresentationFormulas
@[expose] public section

open Real Set MeasureTheory


noncomputable section

namespace CM8

/-- Instance: $2 \le 3$, supplied so that `FundSolN` and related results specialise to the
three-dimensional setting. -/
instance : Fact (2 ≤ 3) := ⟨by omega⟩

end CM8
end
