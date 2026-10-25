/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDualTransverse.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneJoinedArms.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldDualTransverse.Part2
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


theorem PeriodicGraph.finiteSetHitsInfinite_measurableSet
    (P : PeriodicGraph V) (L : Finset V) :
    MeasurableSet (P.finiteSetHitsInfinite L) := by
  have heq : P.finiteSetHitsInfinite L =
      ⋃ x ∈ L, {omega : ConfigSpace (Sym2 V) |
        (P.cluster omega x).Infinite} := by
    ext omega
    simp [PeriodicGraph.finiteSetHitsInfinite]
  rw [heq]
  exact MeasurableSet.iUnion fun x => MeasurableSet.iUnion fun _hx =>
    P.measurableSet_cluster_infinite x

theorem PeriodicGraph.finiteSetHitsInfinite_image_shift
    (P : PeriodicGraph V) (z : Site 2) (n : Nat) :
    P.finiteSetHitsInfinite ((P.orbitBox n).image (P.shift z)) =
      P.translatedOrbitBoxHitsInfinite z n := by
  ext omega
  simp [PeriodicGraph.finiteSetHitsInfinite,
    PeriodicGraph.translatedOrbitBoxHitsInfinite]


end StatMech.FK.PeriodicPlanar
