/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredWeakLimitIdentification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumWeakLimitIdentification.Part6
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.HisingBoxClose.Part3
import Theorem.StatisticalMechanics.Code.FK.InducedBC.Part11
import Theorem.StatisticalMechanics.Code.FK.FreeDLRExtreme
import Def.StatisticalMechanics.Code.FK.PottsClusterSumWiredWeakLimitIdentification.Part4
open Filter MeasureTheory Set Topology


namespace StatMech.FK

open Lattice Percolation

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem connected_extendWiredEdge_of_boxConnected
    {d n : Nat} (omega : ConfigSpace (Sym2 (boxVerts d n)))
    {x y : boxVerts d n}
    (hxy : (openSub (boxGraph d n) omega).Reachable x y) :
    Lattice.Connected d (extendWiredEdge d n omega) (x : Site d) (y : Site d) :=
  hxy.map (boxOpenToExtendWiredOpenHom d n omega)

theorem boundary_adj_extendWiredEdge_exterior
    {d n : Nat} (omega : ConfigSpace (Sym2 (boxVerts d n)))
    {y : boxVerts d n} {z : Site d}
    (hz : z ∈ exterior d n)
    (hyz : (hypercubicLattice d).Adj (y : Site d) z) :
    (openSubgraph d (extendWiredEdge d n omega)).Adj (y : Site d) z := by
  rw [openSubgraph_adj]
  refine ⟨hyz, ?_⟩
  apply extendWiredEdge_eq_true_of_not_range n omega
  intro hrange
  obtain ⟨be, hbe⟩ := hrange
  have hbeEdge : be ∈ (boxGraph d n).edgeFinset :=
    boxEdge_mem n be (y : Site d) z hyz hbe
  have himage : s((y : Site d), z) ∈
      Finset.image (edgeIncl d n) (boxGraph d n).edgeFinset :=
    Finset.mem_image.mpr ⟨be, hbeEdge, hbe⟩
  have hzbox := (IsingFK.hbx_mem_image_edgeIncl_iff d n
    (y : Site d) z).mp himage |>.2.1
  obtain ⟨i, hi⟩ := hz
  exact (not_lt_of_ge (hzbox i)) hi


theorem cluster_extendWiredEdge_infinite_of_connToBdry
    {d n : Nat} (hd : 2 ≤ d) (hn : 1 ≤ n)
    (omega : ConfigSpace (Sym2 (boxVerts d n))) (x : boxVerts d n)
    (hconn : IsingFK.ConnToBdry (boxGraph d n) (boxBoundary d n) omega x) :
    (cluster d (extendWiredEdge d n omega) (x : Site d)).Infinite := by
  obtain ⟨y, hybdry, hxy⟩ := hconn
  obtain ⟨z, hzext, hyz⟩ :=
    exists_exterior_neighbor_of_boxBoundary hn y hybdry
  have hxyFull : Lattice.Connected d (extendWiredEdge d n omega)
      (x : Site d) (y : Site d) :=
    connected_extendWiredEdge_of_boxConnected omega hxy
  have hyzFull : Lattice.Connected d (extendWiredEdge d n omega)
      (y : Site d) z :=
    (boundary_adj_extendWiredEdge_exterior omega hzext hyz).reachable
  apply (exterior_infinite n hd).mono
  intro w hw
  have hzwExterior := box_exterior_connected n hd z w hzext hw
  have hzwFull := hzwExterior.map (exteriorToExtendWiredOpenHom d n omega)
  exact hxyFull.trans (hyzFull.trans hzwFull)

theorem boxOpen_of_extendWiredOpen
    {d n : Nat} (omega : ConfigSpace (Sym2 (boxVerts d n)))
    {x y : boxVerts d n}
    (hxy : (openSubgraph d (extendWiredEdge d n omega)).Adj
      (x : Site d) (y : Site d)) :
    (openSub (boxGraph d n) omega).Adj x y := by
  rw [openSubgraph_adj] at hxy
  rw [openSub_adj]
  constructor
  · simpa [boxGraph] using hxy.1
  · have heq : s((x : Site d), (y : Site d)) =
        edgeIncl d n s(x, y) := by
      simp [edgeIncl]
    rw [heq, extendWiredEdge_eq_of_range] at hxy
    exact hxy.2

theorem connToBdry_of_extendWired_connected_outside
    {d n : Nat} (hn : 1 ≤ n)
    (omega : ConfigSpace (Sym2 (boxVerts d n))) (x : boxVerts d n)
    {v : Site d} (hv : v ∉ box d n)
    (hreach : (openSubgraph d (extendWiredEdge d n omega)).Reachable
      (x : Site d) v) :
    IsingFK.ConnToBdry (boxGraph d n) (boxBoundary d n) omega x := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  let OS := openSubgraph d (extendWiredEdge d n omega)
  let os := openSub (boxGraph d n) omega
  suffices H : ∀ w : Site d, Relation.ReflTransGen OS.Adj (x : Site d) w ->
      (IsingFK.ConnToBdry (boxGraph d n) (boxBoundary d n) omega x ∨
        ∃ y : boxVerts d n, (y : Site d) = w ∧ os.Reachable x y) by
    rcases H v hreach with hdone | ⟨y, hy, hxy⟩
    · exact hdone
    · exact absurd (hy ▸ y.2) hv
  intro w hw
  induction hw with
  | refl =>
      exact Or.inr ⟨x, rfl, SimpleGraph.Reachable.refl _⟩
  | @tail u w huw hadj ih =>
      rcases ih with hdone | ⟨y, hy, hxy⟩
      · exact Or.inl hdone
      · subst hy
        by_cases hwbox : w ∈ box d n
        · let wb : boxVerts d n := ⟨w, hwbox⟩
          refine Or.inr ⟨wb, rfl, hxy.trans ?_⟩
          exact (boxOpen_of_extendWiredOpen omega hadj).reachable
        · left
          rw [openSubgraph_adj] at hadj
          exact ⟨y,
            ⟨y.2, notMem_box_pred_of_adj_outer hn y.2 hadj.1 hwbox⟩,
            hxy⟩

theorem connToBdry_or_boxConnected_of_extendWired_connected
    {d n : Nat} (hn : 1 ≤ n)
    (omega : ConfigSpace (Sym2 (boxVerts d n))) (x y : boxVerts d n)
    (hreach : (openSubgraph d (extendWiredEdge d n omega)).Reachable
      (x : Site d) (y : Site d)) :
    IsingFK.ConnToBdry (boxGraph d n) (boxBoundary d n) omega x ∨
      (openSub (boxGraph d n) omega).Reachable x y := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  let OS := openSubgraph d (extendWiredEdge d n omega)
  let os := openSub (boxGraph d n) omega
  have H : ∀ w : Site d, Relation.ReflTransGen OS.Adj (x : Site d) w ->
      (IsingFK.ConnToBdry (boxGraph d n) (boxBoundary d n) omega x ∨
        ∃ z : boxVerts d n, (z : Site d) = w ∧ os.Reachable x z) := by
    intro w hw
    induction hw with
    | refl => exact Or.inr ⟨x, rfl, SimpleGraph.Reachable.refl _⟩
    | @tail u w huw hadj ih =>
        rcases ih with hdone | ⟨z, hz, hxz⟩
        · exact Or.inl hdone
        · subst hz
          by_cases hwbox : w ∈ box d n
          · let wb : boxVerts d n := ⟨w, hwbox⟩
            refine Or.inr ⟨wb, rfl, hxz.trans ?_⟩
            exact (boxOpen_of_extendWiredOpen omega hadj).reachable
          · left
            rw [openSubgraph_adj] at hadj
            exact ⟨z,
              ⟨z.2, notMem_box_pred_of_adj_outer hn z.2 hadj.1 hwbox⟩,
              hxz⟩
  rcases H (y : Site d) hreach with hconn | ⟨z, hz, hxz⟩
  · exact Or.inl hconn
  · right
    have hzy : z = y := Subtype.ext hz
    simpa [hzy] using hxz


theorem cluster_extendWiredEdge_finite_of_not_connToBdry
    {d n : Nat} (hn : 1 ≤ n)
    (omega : ConfigSpace (Sym2 (boxVerts d n))) (x : boxVerts d n)
    (hconn : ¬ IsingFK.ConnToBdry (boxGraph d n) (boxBoundary d n) omega x) :
    (cluster d (extendWiredEdge d n omega) (x : Site d)).Finite := by
  apply (box_finite d n).subset
  intro y hy
  by_contra hybox
  exact hconn (connToBdry_of_extendWired_connected_outside
    hn omega x hybox (mem_cluster.mp hy))


theorem cluster_extendWiredEdge_infinite_iff_connToBdry
    {d n : Nat} (hd : 2 ≤ d) (hn : 1 ≤ n)
    (omega : ConfigSpace (Sym2 (boxVerts d n))) (x : boxVerts d n) :
    (cluster d (extendWiredEdge d n omega) (x : Site d)).Infinite ↔
      IsingFK.ConnToBdry (boxGraph d n) (boxBoundary d n) omega x := by
  constructor
  · intro hinf
    by_contra hconn
    exact hinf (cluster_extendWiredEdge_finite_of_not_connToBdry
      hn omega x hconn)
  · exact cluster_extendWiredEdge_infinite_of_connToBdry hd hn omega x

theorem boundary_connected_extendWiredEdge
    {d n : Nat} (hd : 2 ≤ d) (hn : 1 ≤ n)
    (omega : ConfigSpace (Sym2 (boxVerts d n)))
    (x y : boxVerts d n) (hx : boxBoundary d n x) (hy : boxBoundary d n y) :
    Lattice.Connected d (extendWiredEdge d n omega) (x : Site d) (y : Site d) := by
  obtain ⟨zx, hzxExt, hxzx⟩ :=
    exists_exterior_neighbor_of_boxBoundary hn x hx
  obtain ⟨zy, hzyExt, hyzy⟩ :=
    exists_exterior_neighbor_of_boxBoundary hn y hy
  have hxzxFull : Lattice.Connected d (extendWiredEdge d n omega)
      (x : Site d) zx :=
    (boundary_adj_extendWiredEdge_exterior omega hzxExt hxzx).reachable
  have hzyyFull : Lattice.Connected d (extendWiredEdge d n omega)
      zy (y : Site d) :=
    (boundary_adj_extendWiredEdge_exterior omega hzyExt hyzy).reachable.symm
  have hzxzyExterior := box_exterior_connected n hd zx zy hzxExt hzyExt
  have hzxzyFull := hzxzyExterior.map (exteriorToExtendWiredOpenHom d n omega)
  exact hxzxFull.trans (hzxzyFull.trans hzyyFull)

theorem wiredSub_adj_connected_extendWiredEdge
    {d n : Nat} (hd : 2 ≤ d) (hn : 1 ≤ n)
    (omega : ConfigSpace (Sym2 (boxVerts d n)))
    {x y : boxVerts d n}
    (hxy : (IsingFK.wiredSub (boxGraph d n) (boxBoundary d n) omega).Adj x y) :
    Lattice.Connected d (extendWiredEdge d n omega) (x : Site d) (y : Site d) := by
  rw [IsingFK.wiredSub, SimpleGraph.sup_adj] at hxy
  rcases hxy with hopen | hboundary
  · exact (boxOpen_adj_extendWiredEdge omega hopen).reachable
  · rw [boundaryCliqueGraph_adj] at hboundary
    exact boundary_connected_extendWiredEdge hd hn omega x y
      hboundary.2.1 hboundary.2.2


theorem wiredSub_reachable_connected_extendWiredEdge
    {d n : Nat} (hd : 2 ≤ d) (hn : 1 ≤ n)
    (omega : ConfigSpace (Sym2 (boxVerts d n)))
    {x y : boxVerts d n}
    (hxy : (IsingFK.wiredSub (boxGraph d n) (boxBoundary d n) omega).Reachable x y) :
    Lattice.Connected d (extendWiredEdge d n omega) (x : Site d) (y : Site d) := by
  unfold Lattice.Connected
  rw [SimpleGraph.reachable_iff_reflTransGen] at hxy
  induction hxy with
  | refl => exact SimpleGraph.Reachable.refl _
  | @tail u v huv hadj ih =>
      exact ih.trans (wiredSub_adj_connected_extendWiredEdge hd hn omega hadj)


theorem extendWiredNonboundaryRepresentatives_law
    {d n q : Nat} [NeZero q] (hd : 2 ≤ d) (hn : 1 ≤ n)
    (boundaryColor : Fin q)
    (omega : ConfigSpace (Sym2 (boxVerts d n)))
    (v0 : boxVerts d n) (hv0 : boxBoundary d n v0) :
    let W := IsingFK.wiredSub (boxGraph d n) (boxBoundary d n) omega
    let c0 := W.connectedComponentMk v0
    let K := {C : W.ConnectedComponent // C ≠ c0}
    let r : K -> Site d := fun C => (C.1.out : boxVerts d n)
    Measure.map (fun label C =>
        pottsClusterSumSpin boundaryColor (extendWiredEdge d n omega)
          label (r C))
      (pottsIIDLabelMeasure d q) =
        Measure.infinitePi fun _ : K =>
          (PMF.uniformOfFintype (Fin q)).toMeasure := by
  dsimp only
  let W := IsingFK.wiredSub (boxGraph d n) (boxBoundary d n) omega
  let c0 := W.connectedComponentMk v0
  let K := {C : W.ConnectedComponent // C ≠ c0}
  let r : K -> Site d := fun C => (C.1.out : boxVerts d n)
  have hnotconn (C : K) :
      ¬ IsingFK.ConnToBdry (boxGraph d n) (boxBoundary d n) omega C.1.out := by
    intro hconn
    have heq := (IsingFK.connToBdry_iff_componentMk_eq
      (boxGraph d n) (boxBoundary d n) v0 hv0 omega C.1.out).mp hconn
    apply C.2
    calc
      C.1 = W.connectedComponentMk C.1.out := (Quot.out_eq C.1).symm
      _ = c0 := heq
  have hfinite : ∀ C : K,
      (cluster d (extendWiredEdge d n omega) (r C)).Finite := by
    intro C
    exact cluster_extendWiredEdge_finite_of_not_connToBdry hn omega C.1.out
      (hnotconn C)
  have hdistinct : ∀ C D : K, C ≠ D ->
      ¬ Lattice.Connected d (extendWiredEdge d n omega) (r C) (r D) := by
    intro C D hCD hfull
    rcases connToBdry_or_boxConnected_of_extendWired_connected
      hn omega C.1.out D.1.out hfull with hconn | hbox
    · exact (hnotconn C hconn).elim
    · apply hCD
      apply Subtype.ext
      have hle : openSub (boxGraph d n) omega ≤ W := by
        dsimp only [W]
        rw [IsingFK.wiredSub]
        exact le_sup_left
      calc
        C.1 = W.connectedComponentMk C.1.out := (Quot.out_eq C.1).symm
        _ = W.connectedComponentMk D.1.out :=
          SimpleGraph.ConnectedComponent.sound (hbox.mono hle)
        _ = D.1 := Quot.out_eq D.1
  exact pottsClusterSumSpin_representatives_law boundaryColor
    (extendWiredEdge d n omega) r hfinite hdistinct

end StatMech.FK
