/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_differagreesets.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.PerOrbitCardClose.Part8
import Theorem.StatisticalMechanics.Code.Walls.rc3_core.Part3
open Finset


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def rc4_differSet (k : ConfigSpace α × ConfigSpace α) : Finset α :=
  Finset.univ.filter (fun a => k.1 a ≠ k.2 a)


def rc4_agreeSet (k : ConfigSpace α × ConfigSpace α) : Finset α :=
  Finset.univ.filter (fun a => k.1 a = k.2 a)

end StatMech.Walls
