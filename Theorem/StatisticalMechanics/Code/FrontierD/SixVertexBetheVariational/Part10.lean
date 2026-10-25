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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheVariational.Part10
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem hasDerivAt_sixVertexBetheOneBodyPotential
    {c : ℝ} (hc : 2 < c) (N : ℕ) (I x : ℝ) :
    HasDerivAt (sixVertexBetheOneBodyPotential c N I)
      (sixVertexBetheOneBodyCoefficient c N I x) x := by
  apply intervalIntegral.integral_hasDerivAt_right
  · exact (continuous_sixVertexBetheOneBodyCoefficient hc N I).intervalIntegrable 0 x
  · exact Continuous.stronglyMeasurableAtFilter
      (continuous_sixVertexBetheOneBodyCoefficient hc N I)
      MeasureTheory.volume (𝓝 x)
  · exact (continuous_sixVertexBetheOneBodyCoefficient hc N I).continuousAt


end
end StatMech.FrontierD
