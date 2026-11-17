/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTwoCycleCapacityHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairedBranchResidualHall.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexTwoCycleCapacityHall.Part2
open Finset


namespace StatMech.FrontierD

public noncomputable section

structure SixVertexPairFineUnionKey (T : EvenTorus) where
  fine : SixVertexHorizontalBoundedFineRowProfile T
  horizontal : T.Vertex -> Fin 3
  vertical : T.Vertex -> Fin 3
deriving DecidableEq, Fintype

end
end StatMech.FrontierD
