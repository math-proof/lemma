module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierEvaluation.Part5
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.ContinuousMap.Compact
public import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierDensity.Part2
open Filter Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierDensity.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

theorem continuous_sixVertexFourierRootDensity
    {lam : Real} (hlam : 0 < lam) :
    Continuous (sixVertexFourierRootDensity lam) := by
  apply continuous_const.add
  apply continuous_tsum
  · intro n
    unfold sixVertexFourierRootDensityTerm
    fun_prop
  · exact summable_sixVertexFourierRootDensityMajorant hlam
  · intro n alpha
    exact norm_sixVertexFourierRootDensityTerm_le hlam n alpha

end
end StatMech.FrontierD
