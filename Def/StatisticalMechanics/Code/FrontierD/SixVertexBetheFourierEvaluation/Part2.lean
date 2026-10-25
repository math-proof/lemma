/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierEvaluation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheBulkReduction.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFreeEnergyReduction
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierEvaluation
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexFreeEnergyFourierPartialSum (lam : Real) (N : Nat) : Real :=
  sixVertexFreeEnergyKernelFourierCoeff lam 0 *
      sixVertexRootDensityFourierCoeff lam 0 +
    ∑ n ∈ range N, sixVertexFreeEnergyPairedFourierTerm lam n

end
end StatMech.FrontierD
