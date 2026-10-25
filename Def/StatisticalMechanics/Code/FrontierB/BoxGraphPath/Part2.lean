/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoxGraphPath.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.FrontierB.BoxGraphPath
open Set SimpleGraph


namespace StatMech.FrontierB

open Lattice


noncomputable def boxGraphPath (d n : ℕ)
    (x y : StatMech.FK.boxVerts d n) :
    (StatMech.FK.boxGraph d n).Walk x y :=
  (boxGraph_preconnected d n x y).some.toPath

end StatMech.FrontierB
