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

@[expose] public section

open Complex MeasureTheory Metric Set Filter Topology


noncomputable section

def residue (f : ℂ → ℂ) (a : ℂ) (R : ℝ) : ℂ :=
  (2 * ↑Real.pi * I)⁻¹ * (∮ z in C(a, R), f z)

end
