/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareFiniteDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part6
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
open Finset SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC

noncomputable section

def fkSquareBoxPlanar (n : Nat) : PlanarZ2Subgraph where
  V := FK.boxVerts 2 n
  finV := inferInstance
  decV := inferInstance
  G := FK.boxGraph 2 n
  emb := Function.Embedding.subtype _
  isSub := by
    intro x y hxy
    exact hxy

end
end StatMech.FrontierD
