module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEquations.Part7
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheVariational.Part8
open Finset Filter Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVariational.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def sixVertexBetheOneBodyCoefficient
    (c : ℝ) (N : ℕ) (I x : ℝ) : ℝ :=
  ((N : ℝ) * x - 2 * Real.pi * I) /
    sixVertexBetheIntegratingFactor c x

end
end StatMech.FrontierD
