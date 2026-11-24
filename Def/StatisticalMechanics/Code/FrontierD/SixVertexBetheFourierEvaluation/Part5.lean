module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheBulkReduction.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFreeEnergyReduction
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierEvaluation.Part4
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

def SixVertexFixedChargeMatchesOffsetFourier
    (c : Real) (r : Nat) : Prop :=
  Tendsto (fun k => sixVertexFixedChargeLogRatio c r k +
      (r : Real) * sixVertexOffsetFourierPartialSum
        (sixVertexAntiferroelectricLambda c) k)
    atTop (nhds 0)


end
end StatMech.FrontierD
