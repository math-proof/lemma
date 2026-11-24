module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexTwoCycleCapacityHall.Part4
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSectorPerronLogConcavity.Part3
open Filter Matrix Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveEvenTraceLogConcavity.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def sixVertexPositiveEvenHeight (M : Nat) : Nat := 2 * (M + 1)

end
end StatMech.FrontierD
