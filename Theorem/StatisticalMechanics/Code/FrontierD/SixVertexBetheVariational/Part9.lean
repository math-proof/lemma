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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheVariational.Part9
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem continuous_sixVertexBetheOneBodyCoefficient
    {c : ℝ} (hc : 2 < c) (N : ℕ) (I : ℝ) :
    Continuous (sixVertexBetheOneBodyCoefficient c N I) := by
  unfold sixVertexBetheOneBodyCoefficient sixVertexBetheIntegratingFactor
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro x
    exact (sixVertexBetheIntegratingFactor_pos hc x).ne'


end
end StatMech.FrontierD
