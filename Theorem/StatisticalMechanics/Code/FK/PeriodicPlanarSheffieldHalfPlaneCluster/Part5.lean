/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCluster.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneExclusion.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRectanglePreference.Part4
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalErgodicity.Part3
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAxisSwap.Part3
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAxisNegation.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneCluster.Part4
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


theorem PeriodicGraph.setHitsInfiniteWithin_configTranslate
    (P : PeriodicGraph V) (z : Site 2)
    (omega : ConfigSpace (Sym2 V)) (A S : Set V) :
    P.configTranslate z omega ∈ P.setHitsInfiniteWithin
        (P.shift z '' A) (P.shift z '' S) ↔
      omega ∈ P.setHitsInfiniteWithin A S := by
  constructor
  · rintro ⟨_, ⟨x, hxS, rfl⟩, hinfinite⟩
    refine ⟨x, hxS, ?_⟩
    rw [← P.clusterWithinSet_configTranslate z omega A x] at hinfinite
    exact hinfinite.of_image (P.shift z)
  · rintro ⟨x, hxS, hinfinite⟩
    refine ⟨P.shift z x, ⟨x, hxS, rfl⟩, ?_⟩
    rw [← P.clusterWithinSet_configTranslate z omega A x]
    exact hinfinite.image (P.shift z).injective.injOn

theorem PeriodicGraph.setHitsInfiniteWithin_measurableSet
    (P : PeriodicGraph V) (A S : Set V) :
    MeasurableSet (P.setHitsInfiniteWithin A S) := by
  have heq : P.setHitsInfiniteWithin A S =
      ⋃ x : V, ⋃ (_hx : x ∈ S),
        {omega : ConfigSpace (Sym2 V) |
          (P.clusterWithinSet omega A x).Infinite} := by
    ext omega
    simp [PeriodicGraph.setHitsInfiniteWithin]
  rw [heq]
  exact MeasurableSet.iUnion fun x => MeasurableSet.iUnion fun _hx =>
    P.measurableSet_clusterWithinSet_infinite A x

theorem PeriodicGraph.setHitsInfiniteWithin_translate_measureReal_eq
    (P : PeriodicGraph V)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (hTI : P.IsTranslationInvariant mu) (z : Site 2) (A S : Set V) :
    mu.real (P.setHitsInfiniteWithin (P.shift z '' A) (P.shift z '' S)) =
      mu.real (P.setHitsInfiniteWithin A S) := by
  have hpre : P.configTranslate z ⁻¹'
      P.setHitsInfiniteWithin (P.shift z '' A) (P.shift z '' S) =
        P.setHitsInfiniteWithin A S := by
    ext omega
    exact P.setHitsInfiniteWithin_configTranslate z omega A S
  calc
    mu.real (P.setHitsInfiniteWithin (P.shift z '' A) (P.shift z '' S)) =
        mu.real (P.configTranslate z ⁻¹'
          P.setHitsInfiniteWithin (P.shift z '' A) (P.shift z '' S)) := by
      exact congrArg ENNReal.toReal ((hTI z).measure_preimage
        (P.setHitsInfiniteWithin_measurableSet
          (P.shift z '' A) (P.shift z '' S)).nullMeasurableSet).symm
    _ = mu.real (P.setHitsInfiniteWithin A S) := by rw [hpre]


end StatMech.FK.PeriodicPlanar
