/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredTranslatedBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumWiredTruncation
import Theorem.StatisticalMechanics.Code.FK.FKGeneralQTranslation.Part2
import Theorem.StatisticalMechanics.Code.IsingFK.PcUpperAllDimensions
import Def.StatisticalMechanics.Code.FK.PottsClusterSumWiredTranslatedBoundary.Part6
open Filter MeasureTheory Set SimpleGraph Topology
open scoped BigOperators


namespace StatMech.FK

open Lattice Percolation IsingFK

noncomputable section

theorem wiredTruncatedInfiniteEvent_eq_preimage
    {d R : Nat} (hd : 2 ≤ d) (hR : 1 ≤ R) (x : Site d)
    (hx : x ∈ box d R) :
    wiredTruncatedInfiniteEvent d R x =
      boxRestrict d R ⁻¹'
        finiteConnToBdryEvent (boxGraph d R) (boxBoundary d R) ⟨x, hx⟩ := by
  ext omega
  change (cluster d (extendWiredEdge d R (boxRestrict d R omega)) x).Infinite ↔
    ConnToBdry (boxGraph d R) (boxBoundary d R)
      (boxRestrict d R omega) ⟨x, hx⟩
  exact cluster_extendWiredEdge_infinite_iff_connToBdry
    hd hR (boxRestrict d R omega) ⟨x, hx⟩

theorem isClopen_wiredTruncatedInfiniteEvent
    {d R : Nat} (hd : 2 ≤ d) (hR : 1 ≤ R) (x : Site d)
    (hx : x ∈ box d R) :
    IsClopen (wiredTruncatedInfiniteEvent d R x) := by
  rw [wiredTruncatedInfiniteEvent_eq_preimage hd hR x hx]
  exact (isClopen_discrete _).preimage (continuous_boxRestrict d R)

theorem measurableSet_wiredTruncatedInfiniteEvent
    {d R : Nat} (hd : 2 ≤ d) (hR : 1 ≤ R) (x : Site d)
    (hx : x ∈ box d R) :
    MeasurableSet (wiredTruncatedInfiniteEvent d R x) :=
  (isClopen_wiredTruncatedInfiniteEvent hd hR x hx).isOpen.measurableSet

end
end StatMech.FK
