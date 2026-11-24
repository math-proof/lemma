module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheRootBounds.Part2
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheBulkReduction
open Finset Filter Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheBulkReduction.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def SixVertexSelectedBulkFreeEnergyAsymptotic
    {c : Real} (hc : 2 < c) : Prop :=
  Tendsto (fun k => sixVertexSelectedBulkLogKernel hc
      (Nat.log2 (k + 1)) k) atTop
    (nhds (sixVertexAntiferroelectricFreeEnergyValue
      (sixVertexAntiferroelectricLambda c)))


end
end StatMech.FrontierD
