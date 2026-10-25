/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/euceuler.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.euceuler.Part2
open scoped BigOperators
open Finset


namespace StatMech.Euc

inductive EucBuildable : Finset Cell → Prop
  | singleton (c : Cell) : EucBuildable {c}
  | attach (c : Cell) (K : Finset Cell) (hK : EucBuildable K) (hc : c ∉ K)
      (harc : newEdges c K = newVerts c K + 1) : EucBuildable (insert c K)


end StatMech.Euc
