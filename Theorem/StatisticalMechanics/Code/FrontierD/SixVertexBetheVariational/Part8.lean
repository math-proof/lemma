module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEquations.Part7
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
public import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheVariational.Part8
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

theorem hasFDerivAt_sixVertexBethePairPotential
    {c : ℝ} (hc : 2 < c) (xy : ℝ × ℝ) :
    HasFDerivAt (sixVertexBethePairPotential hc)
      (sixVertexBethePairOneForm c xy) xy :=
  Classical.choose_spec (exists_sixVertexBethePairPotential hc) xy


end
end StatMech.FrontierD
