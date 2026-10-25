/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.jc2_engine
import Theorem.StatisticalMechanics.Code.Walls.jc2_runframe.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc2_thinpendant
import Theorem.StatisticalMechanics.Code.Walls.jc2_thinconn
import Theorem.StatisticalMechanics.Code.Walls.jc2_thinthickdichotomy.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc2_thickshelf.Part3
import Theorem.StatisticalMechanics.Code.Walls.jc_core
import Theorem.StatisticalMechanics.Code.Lattice.BalancePreservingContraction.Part4
import Theorem.StatisticalMechanics.Code.Walls.jc2_core.Part2
open SimpleGraph Function Set


namespace StatMech

namespace Walls

open StatMech.Lattice


def jc2_SaturatingEarMatch : Prop :=
  ∀ (K : Set (Site 2)), K.Finite → 2 ≤ K.ncard →
    ∀ (a : {e : Dart // IsBoundaryDart K e}),
      K ⊆ bpc_orbitFootprint K a →
      ∀ c len, jc2_RunFrame K c len → jc2_PendantClipMatch K a (c + ![len, 0])


end Walls
end StatMech
