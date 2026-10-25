/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ComplexVariables/code/Lecture14.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.MeasureTheory.Integral.Prod
import Def.v1.Atlas.ComplexVariables.code.Lecture13.Part2
import Lemma.Complex.Atlas.v1.ComplexVariables.code.Lecture13
import Lemma.Complex.Atlas.v1.ComplexVariables.code.CauchyTransformDiff
open Complex MeasureTheory Metric Set Filter Topology


noncomputable section

def residue (f : ℂ → ℂ) (a : ℂ) (R : ℝ) : ℂ :=
  (2 * ↑Real.pi * I)⁻¹ * (∮ z in C(a, R), f z)

end
