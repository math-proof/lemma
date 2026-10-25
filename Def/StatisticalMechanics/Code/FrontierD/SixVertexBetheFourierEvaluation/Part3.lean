/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierEvaluation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheBulkReduction.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFreeEnergyReduction
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierEvaluation.Part2
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexOffsetFourierPartialSum (lam : Real) (N : Nat) : Real :=
  lam - ∑ n ∈ range N,
      (-1 : Real) ^ (n + 1) *
        (Real.exp (-2 * (n + 1 : Real) * lam) - 1) / (n + 1 : Real) -
    ∑ n ∈ range N,
      (-1 : Real) ^ (n + 1) * Real.tanh ((n + 1 : Real) * lam) *
        (Real.exp (-2 * (n + 1 : Real) * lam) - 1) / (n + 1 : Real)

end
end StatMech.FrontierD
