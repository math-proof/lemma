/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoverage.Part3
import Theorem.StatisticalMechanics.Code.FK.ContinuousRectangleCrossing.Part9
import Theorem.StatisticalMechanics.Code.Foundations.Ergodicity.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffield.Part14
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


@[simp] theorem PeriodicGraph.openSubgraphTranslateHom_apply
    (P : PeriodicGraph V) (z : Site 2)
    (omega : ConfigSpace (Sym2 V)) (x : V) :
    P.openSubgraphTranslateHom z omega x = P.shift z x := rfl

theorem PeriodicGraph.reachable_configTranslate
    (P : PeriodicGraph V) (z : Site 2)
    (omega : ConfigSpace (Sym2 V)) (x y : V) :
    (P.openSubgraph (P.configTranslate z omega)).Reachable
        (P.shift z x) (P.shift z y) ↔
      (P.openSubgraph omega).Reachable x y := by
  constructor
  · intro h
    have hmapped := h.map
      (P.openSubgraphTranslateHom (-z) (P.configTranslate z omega))
    simpa [PeriodicGraph.configTranslate, P.shift_neg_shift] using hmapped
  · exact fun h => h.map (P.openSubgraphTranslateHom z omega)

theorem PeriodicGraph.cluster_configTranslate
    (P : PeriodicGraph V) (z : Site 2)
    (omega : ConfigSpace (Sym2 V)) (x : V) :
    P.cluster (P.configTranslate z omega) (P.shift z x) =
      P.shift z '' P.cluster omega x := by
  ext y
  constructor
  · intro hy
    refine ⟨P.shift (-z) y, ?_, P.shift_shift_neg z y⟩
    have hreach :
        (P.openSubgraph (P.configTranslate z omega)).Reachable
          (P.shift z x) (P.shift z (P.shift (-z) y)) := by
      simpa using hy
    exact (P.reachable_configTranslate z omega x (P.shift (-z) y)).mp hreach
  · rintro ⟨y, hy, rfl⟩
    exact (P.reachable_configTranslate z omega x y).mpr hy

theorem PeriodicGraph.cluster_infinite_configTranslate
    (P : PeriodicGraph V) (z : Site 2)
    (omega : ConfigSpace (Sym2 V)) (x : V) :
    (P.cluster (P.configTranslate z omega) (P.shift z x)).Infinite ↔
      (P.cluster omega x).Infinite := by
  rw [P.cluster_configTranslate z omega x]
  exact Set.infinite_image_iff
    (Set.injOn_of_injective (P.shift z).injective)


end StatMech.FK.PeriodicPlanar
