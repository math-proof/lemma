/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVariational.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEquations.Part7
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheVariational.Part8
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexBetheOneBodyCoefficient
    (c : ℝ) (N : ℕ) (I x : ℝ) : ℝ :=
  ((N : ℝ) * x - 2 * Real.pi * I) /
    sixVertexBetheIntegratingFactor c x

end
end StatMech.FrontierD
