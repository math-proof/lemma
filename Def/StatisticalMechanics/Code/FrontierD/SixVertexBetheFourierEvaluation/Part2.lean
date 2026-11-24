module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheBulkReduction.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFreeEnergyReduction
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierEvaluation
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

def sixVertexFreeEnergyFourierPartialSum (lam : Real) (N : Nat) : Real :=
  sixVertexFreeEnergyKernelFourierCoeff lam 0 *
      sixVertexRootDensityFourierCoeff lam 0 +
    ∑ n ∈ range N, sixVertexFreeEnergyPairedFourierTerm lam n

end
end StatMech.FrontierD
