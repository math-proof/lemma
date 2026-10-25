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
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheVariational.Part4
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexNormalizedBetheResidual (c : ℝ) (N n : ℕ)
    (p : Fin n → ℝ) (j : Fin n) : ℝ :=
  sixVertexBetheResidual c N n p j /
    sixVertexBetheIntegratingFactor c (p j)

end
end StatMech.FrontierD
