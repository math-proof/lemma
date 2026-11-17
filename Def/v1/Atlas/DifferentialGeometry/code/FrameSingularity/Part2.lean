/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/FrameSingularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Structure.v1.Atlas.DifferentialGeometry.code.FrameSingularity

@[expose] public section

noncomputable section

namespace FrameSingularity

open Real Complex

def dTheta (p : ℝ × ℝ) : ℝ × ℝ :=
  (-(p.2) / (p.1 ^ 2 + p.2 ^ 2), p.1 / (p.1 ^ 2 + p.2 ^ 2))

open Filter Topology MeasureTheory

def circleIntegral1Form (α : ℝ × ℝ → ℝ × ℝ) (ρ : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..(2 * π),
    let p := (ρ * Real.cos t, ρ * Real.sin t)
    let tangent := (-ρ * Real.sin t, ρ * Real.cos t)
    (α p).1 * tangent.1 + (α p).2 * tangent.2

end FrameSingularity
end
