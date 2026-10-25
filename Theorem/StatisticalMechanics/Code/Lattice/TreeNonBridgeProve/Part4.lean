/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNonBridgeProve.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces.Part3
import Theorem.StatisticalMechanics.Code.Lattice.FloodFillConnected.Part3
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ArcNoSeparation.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ArcExteriorClose.Part3
import Def.StatisticalMechanics.Code.Lattice.TreeNonBridgeProve.Part3
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

variable {V : Type*}


@[simp] theorem tnbp_ringChain_nil : tnbp_RingChain [] := trivial

theorem tnbp_ringChain_cons {c : Site 2} {L' : List (Site 2)}
    (hhead : tnbp_RingConnected c {x : Site 2 | x ∈ L'}) (htail : tnbp_RingChain L') :
    tnbp_RingChain (c :: L') := ⟨hhead, htail⟩


theorem tnbp_reachesExterior_ringChain {R : ℕ} :
    ∀ {L : List (Site 2)}, (∀ c ∈ L, c ∈ box 2 R) → tnbp_RingChain L →
      arcxc_ReachesExterior {x : Site 2 | x ∈ L} R := by
  intro L
  induction L with
  | nil =>
    intro _ _
    have hset : {x : Site 2 | x ∈ ([] : List (Site 2))} = (∅ : Set (Site 2)) := by
      ext z; simp
    rw [hset]; exact tnbp_empty_reachesExterior R
  | cons c L' ih =>
    intro hbox hchain
    obtain ⟨hringHead, htail⟩ := hchain
    have hboxL' : ∀ d ∈ L', d ∈ box 2 R := fun d hd => hbox d (List.mem_cons_of_mem _ hd)
    have hbaseL' : arcxc_ReachesExterior {x : Site 2 | x ∈ L'} R := ih hboxL' htail
    have hset : {x : Site 2 | x ∈ c :: L'} = insert c {x : Site 2 | x ∈ L'} := by
      ext z; simp [List.mem_cons]
    rw [hset]
    exact tnbp_reachesExterior_insert_of_ringConnected hbaseL'
      (hbox c List.mem_cons_self) hringHead


theorem tnbp_ringClear_singleton (c : Site 2) : tnbp_RingClear c (∅ : Set (Site 2)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · rw [Set.mem_insert_iff]
      refine fun hmem => ?_
      rcases hmem with h | h
      · have h0 := congrFun h 0
        have h1 := congrFun h 1
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
        omega
      · exact Set.notMem_empty _ h


theorem tnbp_ringChain_singleton (c : Site 2) : tnbp_RingChain [c] :=
  tnbp_ringChain_cons
    (by
      have := tnbp_neighbours_connected_of_ringClear (tnbp_ringClear_singleton c)
      simpa using this)
    tnbp_ringChain_nil


theorem tnbp_singlePoint_reachesExterior {c : Site 2} {R : ℕ} (hc : c ∈ box 2 R) :
    arcxc_ReachesExterior ({c} : Set (Site 2)) R := by
  have hset : {x : Site 2 | x ∈ [c]} = ({c} : Set (Site 2)) := by ext z; simp
  rw [← hset]
  refine tnbp_reachesExterior_ringChain ?_ (tnbp_ringChain_singleton c)
  intro d hd; rw [List.mem_singleton] at hd; exact hd ▸ hc


theorem tnbp_singlePoint_connected (c : Site 2) :
    arcns_OffSupportConnected ({c} : Set (Site 2)) := by
  obtain ⟨R, hR⟩ := finite_subset_box ({c} : Set (Site 2)) (Set.finite_singleton c)
  exact arcxc_connected_of_reachesExterior
    (tnbp_singlePoint_reachesExterior (hR (Set.mem_singleton c)))


theorem tnbp_singlePoint_nonvacuous :
    (ffc_offSupportLattice ({![0, 0]} : Set (Site 2))).Reachable ![1, 0] ![0, 1] := by
  apply tnbp_singlePoint_connected
  · simp only [Set.mem_singleton_iff]; intro h; have := congrFun h 0; simp at this
  · simp only [Set.mem_singleton_iff]; intro h; have := congrFun h 1; simp at this


theorem tnbp_reachesExterior_insert_of_ringClear {B : Set (Site 2)} {R : ℕ} {c : Site 2}
    (hbase : arcxc_ReachesExterior B R) (hc : c ∈ box 2 R) (hclear : tnbp_RingClear c B) :
    arcxc_ReachesExterior (insert c B) R :=
  tnbp_reachesExterior_insert_of_ringConnected hbase hc
    (tnbp_neighbours_connected_of_ringClear hclear)

end Lattice
end StatMech
