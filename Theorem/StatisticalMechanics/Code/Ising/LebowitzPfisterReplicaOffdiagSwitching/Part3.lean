/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOffdiagSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaCutParity.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.DeltaBound.Part2
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOffdiagSwitching.Part3
open Finset
open scoped BigOperators symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplica_sourcePairDisconnSum_offdiag_eq_sum_slices
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (beta : Real) (J : Sym2 (LPReplicaCurrentVertex V) -> Real) :
    sourcePairDisconnSum (lpReplicaCurrentGraph G sites) beta J
        (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1)
        ∅ lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 =
      ∑ k : I, lpReplicaOffdiagDisconnSlice
        G sites hsite i j hij beta J k := by
  let H := lpReplicaCurrentGraph G sites
  let A := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
    lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
    lpMatchingGhostSource
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
      lpReplicaCurrentGhost1
  let sel := lpReplicaOffdiagSeamSelector G sites hsite i j hij
  have hpart := lp_gatedSourcePairSum_partition_fintype H beta J A ∅
    (fun n => ¬ CurrentConnected H n
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) sel
  have hadd (k : I) :
      gatedSourcePairSum H beta J A ∅ (fun n =>
          sel n = k ∧ ¬ CurrentConnected H n
            lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) =
        gatedSourcePairSum H beta J A ∅ (fun n =>
          (sel n = k ∧ ¬ CurrentConnected H n
            lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) ∧
          CurrentConnected H n
            (lpReplicaCurrentLeft sites k)
            (lpReplicaCurrentRight sites k)) := by
    apply gatedSourcePairSum_congr_sources
    intro p q hp hq
    have htotal : StatMech.Sharpness.sources H
        (ofEdgeFun H (fun e => p e + q e)) = A := by
      rw [← ofEdgeFun_add,
        StatMech.Sharpness.sources_add H
          (ofEdgeFun H p) (ofEdgeFun H q), hp, hq]
      simp
    have hconn := lpReplicaOffdiagSeamSelector_connected
      G sites hsite hij (fun e => p e + q e) htotal
    constructor
    · intro h
      refine ⟨h, ?_⟩
      rw [← h.1]
      exact hconn
    · exact fun h => h.1
  change gatedSourcePairSum H beta J A ∅ (fun n =>
      ¬ CurrentConnected H n lpReplicaCurrentGhost0
        lpReplicaCurrentGhost1) = _
  rw [hpart]
  apply Finset.sum_congr rfl
  intro k _
  rw [hadd k]
  rfl


theorem lpReplica_sourcePairDisconnSum_offdiag_eq_sum_toggled
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (beta : Real) (J : Sym2 (LPReplicaCurrentVertex V) -> Real) :
    let H := lpReplicaCurrentGraph G sites
    let A := lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
      lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
      lpMatchingGhostSource
        (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
        lpReplicaCurrentGhost1
    sourcePairDisconnSum H beta J A ∅
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 =
      ∑ k : I, gatedSourcePairSum H beta J
        (A ∆ lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) k)
        (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) k)
        (fun n =>
          (lpReplicaOffdiagSeamSelector G sites hsite i j hij n = k ∧
            ¬ CurrentConnected H n
              lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) ∧
          CurrentConnected H n
            (lpReplicaCurrentLeft sites k)
            (lpReplicaCurrentRight sites k)) := by
  dsimp only
  rw [lpReplica_sourcePairDisconnSum_offdiag_eq_sum_slices
    G sites hsite hij beta J]
  apply Finset.sum_congr rfl
  intro k _
  unfold lpReplicaOffdiagDisconnSlice
  let P : Current (LPReplicaCurrentVertex V) -> Prop := fun n =>
    lpReplicaOffdiagSeamSelector G sites hsite i j hij n = k ∧
      ¬ CurrentConnected (lpReplicaCurrentGraph G sites) n
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1
  have htoggle := lpReplica_gatedSourcePairSum_toggle_seam
    G sites beta J
    (lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
      lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
      lpMatchingGhostSource
        (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
        lpReplicaCurrentGhost1)
    ∅ k P
  simpa only [P, bot_symmDiff] using htoggle

end
end StatMech.Ising
