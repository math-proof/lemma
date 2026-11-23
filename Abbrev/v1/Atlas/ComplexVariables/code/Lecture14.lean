/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ComplexVariables/code/Lecture14.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.MeasureTheory.Integral.Prod
public import Def.v1.Atlas.ComplexVariables.code.Lecture13.Part2
public import Theorem.Complex.Atlas.v1.ComplexVariables.code.Lecture13
public import Theorem.Complex.Atlas.v1.ComplexVariables.code.CauchyTransformDiff
public import Def.v1.Atlas.ComplexVariables.code.Lecture14
open Complex MeasureTheory Metric Set Filter Topology


@[expose] public noncomputable section

open Classical in
abbrev singPts {nz np : ℕ} (zeros : Fin nz → ℂ) (poles : Fin np → ℂ) : Fin (nz + np) → ℂ :=
  Fin.addCases zeros poles

abbrev singRads {nz np : ℕ} (rz : Fin nz → ℝ) (rp : Fin np → ℝ) : Fin (nz + np) → ℝ :=
  Fin.addCases rz rp

end
