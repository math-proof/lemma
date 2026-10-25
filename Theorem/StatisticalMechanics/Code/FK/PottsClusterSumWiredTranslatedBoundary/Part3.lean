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
import Def.StatisticalMechanics.Code.FK.PottsClusterSumWiredTranslatedBoundary.Part3
open Filter MeasureTheory Set SimpleGraph Topology
open scoped BigOperators


namespace StatMech.FK

open Lattice Percolation IsingFK

noncomputable section

@[simp] theorem transBoxCenter_val (d n : Nat) (x : Site d) :
    (transBoxCenter d n x : Site d) = x := by
  funext i
  simp [transBoxCenter, boxOrigin, fvs_transEquiv_val, origin]


theorem translated_wiredConnToBdryMass_eq_centered
    {d : Nat} (x : Site d) (n : Nat) (p q : Real) :
    wiredConnToBdryMass (fvs_transBoxGraph d n x)
        (fvs_transBoxBoundary d n x) p q (transBoxCenter d n x) =
      wiredConnToBdryMass (boxGraph d n) (boxBoundary d n) p q
        (boxOrigin d n) := by
  simpa [transBoxCenter] using
    (wiredConnToBdryMass_equiv
      (boxGraph d n) (fvs_transBoxGraph d n x)
      (boxBoundary d n) (fvs_transBoxBoundary d n x)
      (fvs_transEquiv d n x) (fvs_transEquiv_adj d n x)
      (fvs_transEquiv_boundary d n x) p q (boxOrigin d n))


theorem translated_outer_boundaryMass_le_centered_marked
    {d : Nat} (x : Site d) (n : Nat) (hn : 1 ≤ n)
    (hxn : flc_vrad x ≤ n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    wiredConnToBdryMass
        (fvs_transBoxGraph d (n + flc_vrad x + 1) x)
        (fvs_transBoxBoundary d (n + flc_vrad x + 1) x) p q
        (transBoxCenter d (n + flc_vrad x + 1) x) ≤
      wiredConnToBdryMass (boxGraph d n) (boxBoundary d n) p q
        ⟨x, by
          exact fun i => (flc_vrad_le x i).trans hxn⟩ := by
  have hsub : box d n ⊆ fvs_transBox d (n + flc_vrad x + 1) x :=
    flc_box_subset_transBox x (by omega)
  have hdom := wiredConnToBdryMass_outer_le_inner hsub
    (fvs_transBoxBoundary d (n + flc_vrad x + 1) x)
    (boxBoundary d n)
    (flc_hmargin_box_in_transBox x hsub (by omega))
    (flc_hbdryIn_box hn) hp hp1 hq
    (⟨x, fun i => (flc_vrad_le x i).trans hxn⟩ : boxVerts d n)
  have hcenter : flc_incl hsub
      (⟨x, fun i => (flc_vrad_le x i).trans hxn⟩ : boxVerts d n) =
      transBoxCenter d (n + flc_vrad x + 1) x := by
    apply Subtype.ext
    simp
  rw [hcenter] at hdom
  simpa only [boxGraph, fvs_transBoxGraph, transBoxCenter_val] using hdom


theorem centered_marked_boundaryMass_le_translated_inner
    {d : Nat} (x : Site d) (n : Nat) (hn : 1 ≤ n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    wiredConnToBdryMass
        (boxGraph d (n + flc_vrad x + 1))
        (boxBoundary d (n + flc_vrad x + 1)) p q
        ⟨x, box_mono d (by omega) (fun i => flc_vrad_le x i)⟩ ≤
      wiredConnToBdryMass (fvs_transBoxGraph d n x)
        (fvs_transBoxBoundary d n x) p q (transBoxCenter d n x) := by
  have hsub : fvs_transBox d n x ⊆ box d (n + flc_vrad x + 1) :=
    (flc_transBox_subset_box x n).trans (box_mono d (by omega))
  have hdom := wiredConnToBdryMass_outer_le_inner hsub
    (boxBoundary d (n + flc_vrad x + 1))
    (fvs_transBoxBoundary d n x)
    (flc_hmargin_transBox_in_box x hsub)
    (flc_hbdryIn_transBox hn x) hp hp1 hq (transBoxCenter d n x)
  have hcenter : flc_incl hsub (transBoxCenter d n x) =
      (⟨x, box_mono d (by omega) (fun i => flc_vrad_le x i)⟩ :
        boxVerts d (n + flc_vrad x + 1)) := by
    apply Subtype.ext
    simp
  rw [hcenter] at hdom
  simpa only [boxGraph, fvs_transBoxGraph, transBoxCenter_val] using hdom


end
end StatMech.FK
