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
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneCluster.Part3
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


theorem PeriodicGraph.hasInfiniteClusterWithin_mono
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V))
    {A B : Set V} (hAB : A ⊆ B) :
    P.HasInfiniteClusterWithin omega A →
      P.HasInfiniteClusterWithin omega B := by
  rintro ⟨x, hxA, hinfinite⟩
  refine ⟨x, hAB hxA, hinfinite.mono ?_⟩
  intro y hy
  exact P.connectedWithinSet_mono_region hAB x y hy

theorem PeriodicGraph.hasInfiniteClusterWithin_configTranslate
    (P : PeriodicGraph V) (z : Site 2)
    (omega : ConfigSpace (Sym2 V)) (A : Set V) :
    P.HasInfiniteClusterWithin (P.configTranslate z omega)
        (P.shift z '' A) ↔
      P.HasInfiniteClusterWithin omega A := by
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, hinfinite⟩
    refine ⟨x, hx, ?_⟩
    rw [← P.clusterWithinSet_configTranslate z omega A x] at hinfinite
    exact hinfinite.of_image (P.shift z)
  · rintro ⟨x, hx, hinfinite⟩
    refine ⟨P.shift z x, ⟨x, hx, rfl⟩, ?_⟩
    rw [← P.clusterWithinSet_configTranslate z omega A x]
    exact hinfinite.image (P.shift z).injective.injOn

theorem PeriodicGraph.measurableSet_hasInfiniteClusterWithin
    (P : PeriodicGraph V) (A : Set V) :
    MeasurableSet {omega : ConfigSpace (Sym2 V) |
      P.HasInfiniteClusterWithin omega A} := by
  have heq : {omega : ConfigSpace (Sym2 V) |
      P.HasInfiniteClusterWithin omega A} =
      ⋃ x : V, ⋃ (_hx : x ∈ A),
        {omega : ConfigSpace (Sym2 V) |
          (P.clusterWithinSet omega A x).Infinite} := by
    ext omega
    simp [PeriodicGraph.HasInfiniteClusterWithin]
  rw [heq]
  exact MeasurableSet.iUnion fun x => MeasurableSet.iUnion fun _hx =>
    P.measurableSet_clusterWithinSet_infinite A x


end StatMech.FK.PeriodicPlanar
