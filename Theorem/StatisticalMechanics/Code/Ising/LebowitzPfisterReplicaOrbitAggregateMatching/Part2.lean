/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitAggregateMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPooledTraceFiber.Part4
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitCrossToggleMatching.Part8
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOffdiagSwitching.Part3
import Theorem.StatisticalMechanics.Code.Foundations.EqualFiberHall
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitAggregateMatching
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

set_option maxHeartbeats 800000 in


theorem lpReplicaAggregateDecoratedSourceSelectedSeam_connected
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateDecoratedSource G sites q) :
    StatMech.Sharpness.CurrentConnected (lpReplicaCurrentGraph G sites)
      (StatMech.Sharpness.ofEdgeFun
        (lpReplicaCurrentGraph G sites) z.2.2.2.1.1.1)
      (lpReplicaCurrentLeft sites
        (lpReplicaAggregateDecoratedSourceSelectedSeam
          G sites hsite q z))
      (lpReplicaCurrentRight sites
        (lpReplicaAggregateDecoratedSourceSelectedSeam
          G sites hsite q z)) := by
  let i := z.1
  let j := z.2.1
  let atom := z.2.2.2
  let m := atom.1.1.1
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q atom
  let B := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
    lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
    lpMatchingGhostSource
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
      lpReplicaCurrentGhost1
  have hfull : StatMech.Sharpness.RandomCurrent.sources
      (StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites) m) Finset.univ = B := by
    have h := lpReplicaRowGate_fullSources G sites m ∅ B d.1 d.2
    calc
      _ = ∅ ∆ B := h
      _ = B := by
        ext x
        simp [Finset.mem_symmDiff]
  have hsources := StatMech.Sharpness.FluxEdgeCopy.sources_eq
    (G := lpReplicaCurrentGraph G sites) m
      (Finset.univ : Finset
        (StatMech.Sharpness.FluxEdgeCopy.Copy
          (lpReplicaCurrentGraph G sites) m))
  rw [StatMech.Sharpness.FluxEdgeCopy.profileFlux_univ] at hsources
  have hsrc : StatMech.Sharpness.sources (lpReplicaCurrentGraph G sites)
      (StatMech.Sharpness.ofEdgeFun
        (lpReplicaCurrentGraph G sites) m) = B :=
    hsources.symm.trans hfull
  have hconn := lpReplicaOffdiagSeamSelector_connected G sites hsite
    (lpReplicaAggregateDecoratedSource_indices_ne G sites q z) m hsrc
  simpa only [i, j, atom, m, B,
    lpReplicaAggregateDecoratedSourceSelectedSeam] using hconn

set_option maxHeartbeats 800000 in


theorem lpReplicaAggregateDecoratedSourceSelectedSeam_positive
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateDecoratedSource G sites q) :
    0 < StatMech.Sharpness.ofEdgeFun
        (lpReplicaCurrentGraph G sites) z.2.2.2.1.1.1
      (lpReplicaCurrentSeamEdge sites
        (lpReplicaAggregateDecoratedSourceSelectedSeam
          G sites hsite q z)) := by
  let i := z.1
  let j := z.2.1
  let atom := z.2.2.2
  let m := atom.1.1.1
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q atom
  let B := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
    lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
    lpMatchingGhostSource
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
      lpReplicaCurrentGhost1
  have hfull : StatMech.Sharpness.RandomCurrent.sources
      (StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites) m) Finset.univ = B := by
    have h := lpReplicaRowGate_fullSources G sites m ∅ B d.1 d.2
    calc
      _ = ∅ ∆ B := h
      _ = B := by
        ext x
        simp [Finset.mem_symmDiff]
  have hsources := StatMech.Sharpness.FluxEdgeCopy.sources_eq
    (G := lpReplicaCurrentGraph G sites) m
      (Finset.univ : Finset
        (StatMech.Sharpness.FluxEdgeCopy.Copy
          (lpReplicaCurrentGraph G sites) m))
  rw [StatMech.Sharpness.FluxEdgeCopy.profileFlux_univ] at hsources
  have hsrc : StatMech.Sharpness.sources (lpReplicaCurrentGraph G sites)
      (StatMech.Sharpness.ofEdgeFun
        (lpReplicaCurrentGraph G sites) m) = B :=
    hsources.symm.trans hfull
  have hpos := lpReplicaOffdiagSeamSelector_positive G sites hsite
    (lpReplicaAggregateDecoratedSource_indices_ne G sites q z) m hsrc
  simpa only [i, j, atom, m, B,
    lpReplicaAggregateDecoratedSourceSelectedSeam] using hpos


theorem lpReplicaAggregateDecoratedSourceSelectedSeam_exists_copy
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateDecoratedSource G sites q) :
    ∃ c : StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) z.2.2.2.1.1.1,
      c.1.1 = lpReplicaCurrentSeamEdge sites
        (lpReplicaAggregateDecoratedSourceSelectedSeam
          G sites hsite q z) := by
  let H := lpReplicaCurrentGraph G sites
  let m := z.2.2.2.1.1.1
  let k := lpReplicaAggregateDecoratedSourceSelectedSeam
    G sites hsite q z
  have hmem : lpReplicaCurrentSeamEdge sites k ∈ H.edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset]
    unfold lpReplicaCurrentSeamEdge
    rw [SimpleGraph.mem_edgeSet]
    unfold lpReplicaCurrentLeft lpReplicaCurrentRight
    rw [lpReplicaCurrentGraph_adj_left_right_iff]
    exact ⟨k, rfl, rfl⟩
  let e : H.edgeFinset := ⟨lpReplicaCurrentSeamEdge sites k, hmem⟩
  have hpos := lpReplicaAggregateDecoratedSourceSelectedSeam_positive
    G sites hsite q z
  have hpos' : 0 < m e := by
    unfold StatMech.Sharpness.ofEdgeFun at hpos
    rw [dif_pos hmem] at hpos
    simpa only [H, m, k, e] using hpos
  exact ⟨⟨e, ⟨0, hpos'⟩⟩, rfl⟩


end
end StatMech.Ising
