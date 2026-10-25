/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge.Part10
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBlockRepetition.Part2
open Finset


namespace StatMech.FrontierD

def sixVertexRepeatToroidalBoundary {N M a b : ℕ}
    (ξ : SixVertexToroidalBoundary N M) :
    SixVertexToroidalBoundary ((a + 1) * N) ((b + 1) * M) :=
  (fun j => ξ.1 (finProdFinEquiv.symm j).2,
    fun i => ξ.2 (finProdFinEquiv.symm i).2)

end StatMech.FrontierD
