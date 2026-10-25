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
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheVariational.Part3
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexBetheResidual (c : ℝ) (N n : ℕ)
    (p : Fin n → ℝ) (j : Fin n) : ℝ :=
  (N : ℝ) * p j + ∑ k, sixVertexTheta c (p j) (p k) -
    2 * Real.pi * sixVertexCentralQuantumNumber j

end
end StatMech.FrontierD
