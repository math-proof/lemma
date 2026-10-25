/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_downfaceheadout.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ExteriorConnected.Part3
import Theorem.StatisticalMechanics.Code.Walls.kc3_downfaceheadout
open Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice


def kc3_upperHalf : Set (Site 2) := {p | 0 ≤ p 1}


noncomputable def kc3_downDart : Dart :=
  mkDart (0 : Site 2) (![0, -1] : Site 2) (by
    unfold unitWt; rw [Fin.sum_univ_two]; decide)


end Walls
end StatMech
