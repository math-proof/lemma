/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoxGraphPath.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
open Set SimpleGraph


namespace StatMech.FrontierB

open Lattice


def setCoordinates {d : ℕ} (x y : Site d) (T : Finset (Fin d)) : Site d :=
  fun i => if i ∈ T then y i else x i

end StatMech.FrontierB
