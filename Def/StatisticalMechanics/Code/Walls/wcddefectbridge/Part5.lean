/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcddefectbridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.wadangledefect.Part4
import Theorem.StatisticalMechanics.Code.Walls.jc5_singlecycle.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Theorem.StatisticalMechanics.Code.Lattice.BalanceContraction.Part2
import Theorem.StatisticalMechanics.Code.Lattice.GaussBonnet.Part4
import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
import Theorem.StatisticalMechanics.Code.Walls.wcddefectbridge.Part4
open scoped BigOperators
open Finset
open SimpleGraph Function


namespace StatMech

namespace Wcd

open StatMech.Lattice

open StatMech.Wad

open StatMech.Euc


def WcdPivotBridge (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) : Prop :=
  (∀ i < dartOrbitPeriod K a,
      ¬(wcd_frontCell ((dartNext K)^[i] a.1) ∈ K ∧ wcd_sideCell ((dartNext K)^[i] a.1) ∉ K)) ∧
  (Set.InjOn (fun i => wcd_pivot ((dartNext K)^[i] a.1)) (Set.Iio (dartOrbitPeriod K a))) ∧
  (∀ v ∈ regVerts (wcd_toVtxFinset K hK),
      v ∉ (Finset.range (dartOrbitPeriod K a)).image
        (fun i => wcd_pivot ((dartNext K)^[i] a.1)) →
      defect (wcd_toVtxFinset K hK) v = 0)


end Wcd
end StatMech
