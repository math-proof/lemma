/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetFourierPairing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuousOffsetFourier.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierEvaluation.Part5


namespace StatMech.FrontierD

open Finset Filter Topology

noncomputable section

def sixVertexOffsetLogBoundaryPartialSum
    (lam : Real) (N : Nat) : Real :=
  lam - ∑ n ∈ range N,
    (-1 : Real) ^ (n + 1) *
      (Real.exp (-2 * (n + 1 : Real) * lam) - 1) / (n + 1 : Real)

def sixVertexOffsetLogDerivativePartialSum
    (lam : Real) (N : Nat) (alpha : Real) : Real :=
  ∑ n ∈ range N,
    (1 - Real.exp (-2 * (n + 1 : Real) * lam)) *
      Real.sin ((n + 1 : Real) * alpha)

end
end StatMech.FrontierD
