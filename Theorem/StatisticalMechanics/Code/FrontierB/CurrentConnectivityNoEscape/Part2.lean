/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentConnectivityNoEscape.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.CurrentConnectivityDiagonal.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneErgodic
import Def.StatisticalMechanics.Code.FrontierB.CurrentConnectivityNoEscape.Part2
open Filter MeasureTheory Set Topology


namespace StatMech.FrontierB

open Lattice Percolation

variable {d : ℕ}


theorem mem_twoArmDisconnectedTraceEvent
    {m : ℕ} {x y : Site d} {ω : ConfigSpace (Sym2 (Site d))} :
    ω ∈ twoArmDisconnectedTraceEvent m x y ↔
      connBdry d m ω x ∧ connBdry d m ω y ∧
        ω ∉ boxConnectionEvent m x y := by
  simp only [twoArmDisconnectedTraceEvent, Set.mem_diff, Set.mem_inter_iff,
    mem_traceBoundaryConnectionEvent, and_assoc]

theorem isClopen_twoArmDisconnectedTraceEvent (m : ℕ) (x y : Site d) :
    IsClopen (twoArmDisconnectedTraceEvent m x y) :=
  ((isClopen_traceBoundaryConnectionEvent m x).inter
    (isClopen_traceBoundaryConnectionEvent m y)).diff
      (isClopen_boxConnectionEvent m x y)


theorem mem_traceBoundaryConnectionEvent_of_connected_outside
    {m : ℕ} (hm : 1 ≤ m) {ω : ConfigSpace (Sym2 (Site d))} {x z : Site d}
    (hx : x ∈ box d (m - 1)) (hz : z ∉ box d (m - 1))
    (hconn : Connected d ω x z) :
    ω ∈ traceBoundaryConnectionEvent m x := by
  classical
  rw [mem_traceBoundaryConnectionEvent]
  obtain ⟨p⟩ := hconn
  obtain ⟨a, b, ha, hb, hab, ⟨w⟩⟩ :=
    firstExit p (box d (m - 1)) hx hz
  have hxm : x ∈ box d m := box_mono d (by omega) hx
  have ham : a ∈ box d m := box_mono d (by omega) ha
  have hbm : b ∈ box d m := by
    have hstep := adj_box_step (m := m - 1) ha hab.1
    rwa [show m - 1 + 1 = m by omega] at hstep
  have hbBoundary : b ∈ vertexBoundary d m := ⟨hbm, hb⟩
  have hxa : ConnectedWithin d ω (box d m) ⟨x, hxm⟩ ⟨a, ham⟩ :=
    connectedWithin_mono_set' ω (box_mono d (by omega))
      (x := ⟨x, hx⟩) (y := ⟨a, ha⟩) ⟨w⟩
  have habm : (openSubgraphInduce d ω (box d m)).Adj ⟨a, ham⟩ ⟨b, hbm⟩ := by
    simp only [openSubgraphInduce_adj, openSubgraph_adj]
    exact hab
  exact ⟨hxm, b, hbm, hbBoundary,
    hxa.trans (SimpleGraph.Adj.reachable habm)⟩


theorem currentPairTraceBoxGate_diff_subset_twoArm
    {Q : Set (ConfigSpace (Sym2 (Site d)))} {m k : ℕ} {x y : Site d}
    (hm : 1 ≤ m) (hx : x ∈ box d (m - 1)) (hy : y ∈ box d (m - 1))
    (_hmk : m ≤ k) :
    currentPairTraceBoxGate Q k x y \ currentPairTraceBoxGate Q m x y ⊆
      superposedCurrentTrace ⁻¹' twoArmDisconnectedTraceEvent m x y := by
  intro pair hpair
  let ω := superposedCurrentTrace pair
  have hQ : ω ∈ Q := hpair.1.1
  have hk : ω ∈ boxConnectionEvent k x y := hpair.1.2
  have hnotm : ω ∉ boxConnectionEvent m x y := by
    intro hmconn
    exact hpair.2 ⟨hQ, hmconn⟩
  obtain ⟨_, _, hkconn⟩ := hk
  obtain ⟨p⟩ := hkconn.connected
  have hout : ∃ z ∈ p.support, z ∉ box d m := by
    by_contra h
    simp only [not_exists, not_and] at h
    have hsupp : ∀ z ∈ p.support, z ∈ box d m := by
      intro z hz
      by_contra hzout
      exact h z hz hzout
    apply hnotm
    exact ⟨box_mono d (by omega) hx, box_mono d (by omega) hy,
      ⟨p.induce (box d m) hsupp⟩⟩
  obtain ⟨z, hzp, hzout⟩ := hout
  have hzout' : z ∉ box d (m - 1) := fun hz =>
    hzout (box_mono d (by omega) hz)
  have hxz : Connected d ω x z := (p.takeUntil z hzp).reachable
  have hyz : Connected d ω y z := (p.dropUntil z hzp).reverse.reachable
  rw [Set.mem_preimage, mem_twoArmDisconnectedTraceEvent]
  exact ⟨mem_traceBoundaryConnectionEvent.1
      (mem_traceBoundaryConnectionEvent_of_connected_outside hm hx hzout' hxz),
    mem_traceBoundaryConnectionEvent.1
      (mem_traceBoundaryConnectionEvent_of_connected_outside hm hy hzout' hyz),
    hnotm⟩


theorem twoArmDisconnectedTraceEvent_antitone_of_mem
    {m n : ℕ} {x y : Site d} (hm : 1 ≤ m)
    (hx : x ∈ box d (m - 1)) (hy : y ∈ box d (m - 1)) (hmn : m ≤ n) :
    twoArmDisconnectedTraceEvent n x y ⊆
      twoArmDisconnectedTraceEvent m x y := by
  intro ω hω
  rw [mem_twoArmDisconnectedTraceEvent] at hω ⊢
  obtain ⟨⟨_, zx, _, hzxBoundary, hxzx⟩,
    ⟨_, zy, _, hzyBoundary, hyzy⟩, hnconn⟩ := hω
  have hmnPred : m - 1 ≤ n - 1 := Nat.sub_le_sub_right hmn 1
  have hzxout : zx ∉ box d (m - 1) := fun hzx =>
    hzxBoundary.2 (box_mono d hmnPred hzx)
  have hzyout : zy ∉ box d (m - 1) := fun hzy =>
    hzyBoundary.2 (box_mono d hmnPred hzy)
  refine ⟨mem_traceBoundaryConnectionEvent.1
      (mem_traceBoundaryConnectionEvent_of_connected_outside hm hx hzxout hxzx.connected),
    mem_traceBoundaryConnectionEvent.1
      (mem_traceBoundaryConnectionEvent_of_connected_outside hm hy hzyout hyzy.connected), ?_⟩
  intro hmconn
  exact hnconn (boxConnectionEvent_mono x y hmn hmconn)


end StatMech.FrontierB
