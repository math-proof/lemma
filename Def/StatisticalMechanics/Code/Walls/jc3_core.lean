module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Walls.jc2_core.Part3
public import Theorem.StatisticalMechanics.Code.Walls.jc2_runframe.Part2
public import Theorem.StatisticalMechanics.Code.Walls.jc2_thinthickdichotomy.Part2
public import Theorem.StatisticalMechanics.Code.Walls.jc2_thinconn
public import Theorem.StatisticalMechanics.Code.Walls.jc2_thickshelf.Part3
public import Theorem.StatisticalMechanics.Code.Walls.jc3_earfootprint.Part3
public import Theorem.StatisticalMechanics.Code.Walls.jc3_clipsymmdiff
public import Theorem.StatisticalMechanics.Code.Walls.jc3_shelfcell
public import Theorem.StatisticalMechanics.Code.Walls.jc3_tailturneq
public import Theorem.StatisticalMechanics.Code.Lattice.BalancePreservingContraction.Part4
open SimpleGraph Function Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_core.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Walls

open StatMech.Lattice


def jc3_OrbitSpliceDatum (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) : Prop :=
  ∃ (_ : (K \ {r}).Nonempty) (a' : {e : Dart // IsBoundaryDart (K \ {r}) e}) (m m' n : ℕ),
    dartOrbitPeriod K a = m + n ∧
    dartOrbitPeriod (K \ {r}) a' = m' + n ∧
    (∀ i, i < n →
      (dartNext (K \ {r}))^[m' + i] a'.1 = (dartNext K)^[m + i] a.1 ∧
      bpc_NotProbed r ((dartNext K)^[m + i] a.1)) ∧
    jc_windowTurn (K \ {r}) a'.1 0 m' = jc_windowTurn K a.1 0 m


end Walls
end StatMech
