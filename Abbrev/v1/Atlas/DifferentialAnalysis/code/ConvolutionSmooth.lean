/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ConvolutionSmooth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Instance.v1.Atlas.DifferentialAnalysis.code.TestFunctions
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.TestFunctions
public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
open scoped ZeroAtInfty Convolution SchwartzMap ContDiff
open MeasureTheory Filter Topology Function Set TestFunctions
open ContinuousLinearMap


@[expose] public noncomputable section

namespace ConvolutionSmooth

/-- The complex multiplication bilinear map `ℂ × ℂ → ℂ` viewed as an `ℝ`-bilinear
continuous map; used as the bilinear pairing for convolutions in this file. -/
abbrev mulBilin : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ

end ConvolutionSmooth
end
