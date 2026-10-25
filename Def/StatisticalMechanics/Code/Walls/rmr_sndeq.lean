/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_sndeq.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.PerOrbitCardClose.Part8
open Finset


namespace StatMech.Walls

open ConfigSpace StatMech

variable {α : Type*}


def rmr_flip (d : α → Bool) (ω : ConfigSpace α) : ConfigSpace α :=
  fun a => if d a then !ω a else ω a


def rmr_keyFlip (k : ConfigSpace α × ConfigSpace α) : ConfigSpace α → ConfigSpace α :=
  rmr_flip (fun a => decide (k.1 a ≠ k.2 a))


end StatMech.Walls
