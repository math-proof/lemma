/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedShareVerticalRate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexWidthFreeEnergy.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge.Part10
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexBalancedTraceShare (N M : Nat) (c : Real) : Real :=
  Matrix.trace (sixVertexSectorTransfer N (N / 2) c ^ M) /
    sixVertexFixedWidthPartitionSum N M c


end
end StatMech.FrontierD
