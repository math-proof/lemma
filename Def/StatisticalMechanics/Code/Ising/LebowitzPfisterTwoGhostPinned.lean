/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterTwoGhostPinned.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterGhostLift.Part2
import Abbrev.StatisticalMechanics.Code.Ising.LebowitzPfisterTwoGhostPinned
open Finset
open scoped BigOperators


namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {W V : Type*} [Fintype W] [DecidableEq W]
  [Fintype V] [DecidableEq V]


def lpTwoGhostPinnedConfig (tau : ConfigSpace W) :
    ConfigSpace (LPTwoGhostVertex W)
  | .inl x => tau x
  | .inr b => !b

end
end StatMech.Ising
