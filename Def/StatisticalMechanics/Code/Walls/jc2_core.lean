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
open SimpleGraph Function Set


namespace StatMech

namespace Walls

open StatMech.Lattice


def jc2_OrbitMatchAt (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) : Prop :=
  ∃ (K' : Set (Site 2)) (_ : K'.Finite) (_ : K'.Nonempty)
    (a' : {e : Dart // IsBoundaryDart K' e}) (m m' n : ℕ),
    K'.ncard < K.ncard ∧
    dartOrbitPeriod K a = m + n ∧
    dartOrbitPeriod K' a' = m' + n ∧
    (∀ i, i < n →
      turnZ K ((dartNext K)^[m + i] a.1) = turnZ K' ((dartNext K')^[m' + i] a'.1)) ∧
    jc_windowTurn K' a'.1 0 m' = jc_windowTurn K a.1 0 m


end Walls
end StatMech
