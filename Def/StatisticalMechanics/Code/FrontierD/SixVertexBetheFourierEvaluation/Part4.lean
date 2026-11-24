module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheBulkReduction.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFreeEnergyReduction
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierEvaluation.Part3
open Finset Filter Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierEvaluation.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def SixVertexSelectedBulkMatchesRootDensityFourier
    {c : Real} (hc : 2 < c) : Prop :=
  Tendsto (fun k =>
      sixVertexSelectedBulkLogKernel hc (Nat.log2 (k + 1)) k -
        sixVertexFreeEnergyFourierPartialSum
          (sixVertexAntiferroelectricLambda c) k)
    atTop (nhds 0)


end
end StatMech.FrontierD
