/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedBoundaryGluing
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFiniteTorus.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexParticleHole.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge.Part4
open Finset Matrix


namespace StatMech.FrontierD

def svForwardHorizontal {N : Nat} (x y : SixVertexRow N) : SixVertexRow N :=
  fun k => decide (svRowPrefixCount y k < svRowPrefixCount x k)

def svBackwardHorizontal {N : Nat} (x y : SixVertexRow N) : SixVertexRow N :=
  fun k => decide (svRowPrefixCount y k ≤ svRowPrefixCount x k)

end StatMech.FrontierD
