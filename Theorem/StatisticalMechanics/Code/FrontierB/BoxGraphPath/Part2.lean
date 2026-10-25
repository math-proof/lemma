/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoxGraphPath.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Def.StatisticalMechanics.Code.FrontierB.BoxGraphPath.Part2
open Set SimpleGraph


namespace StatMech.FrontierB

open Lattice


theorem boxGraphPath_isPath (d n : ℕ)
    (x y : StatMech.FK.boxVerts d n) :
    (boxGraphPath d n x y).IsPath :=
  SimpleGraph.Path.isPath _

end StatMech.FrontierB
