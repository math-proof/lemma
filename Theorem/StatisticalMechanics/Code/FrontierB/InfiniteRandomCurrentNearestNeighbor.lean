/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteRandomCurrentNearestNeighbor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.CurrentChainClosure
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentSelectionIndependence.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.FreeCurrentFamilyMixing
import Theorem.StatisticalMechanics.Code.FrontierB.PlusCurrentFamilyMixing.Part3
import Structure.StatisticalMechanics.Code.FrontierB.InfiniteRandomCurrentNearestNeighbor
open Filter MeasureTheory Set Topology


namespace StatMech.FrontierB

open Sharpness Ising Lattice Percolation


theorem nearestNeighborInfiniteRandomCurrentPackage
    (d : Nat) (beta : Real) (hbeta : 0 < beta) (hd : 1 <= d) :
    NearestNeighborInfiniteRandomCurrentPackage d beta hbeta hd where
  plus_weak := plusBoxCurrentMeasure_tendsto_full d beta hbeta
  free_weak := freeBoxCurrentMeasure_tendsto_full d beta hbeta
  plus_invariant :=
    infinitePlusCurrentMeasure_isTranslationInvariant d beta hbeta
  free_invariant :=
    infiniteFreeCurrentMeasure_isTranslationInvariant d beta hbeta
  plus_ergodic := infinitePlusCurrentMeasure_isErgodic hd hbeta
  free_ergodic := infiniteFreeCurrentMeasure_isErgodic hd hbeta
  plus_cylinder :=
    plusBoxCurrentMeasure_cylinder_tendsto_full d beta hbeta
  free_cylinder :=
    freeBoxCurrentMeasure_cylinder_tendsto_full d beta hbeta
  mixed_switching := fun N x y hx hy hxy Q hQ =>
    infinitePlusFreeSource_switching
      d N hd beta hbeta x y hx hy hxy Q hQ

end StatMech.FrontierB
