/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/MatchedConnectivityInterior.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.JordanInteriorLib.Part4
import Theorem.StatisticalMechanics.Code.Lattice.InteriorWindingClose
import Theorem.StatisticalMechanics.Code.Lattice.SegmentDownClose.Part2
import Def.StatisticalMechanics.Code.Lattice.MatchedConnectivityInterior.Part4
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem mci_interiorKingGraph_axial_adj {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {u v : jil_offSupportInterior Vc}
    (hadj : (hypercubicLattice 2).Adj (u : Site 2) (v : Site 2)) :
    (mci_interiorKingGraph Vc).Adj u v := by
  rw [mci_interiorKingGraph, SimpleGraph.induce_adj]
  exact mci_hyper_le_king hadj


theorem mci_interiorKingGraph_adj {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {u v : jil_offSupportInterior Vc}
    (hadj : mci_kingGraph.Adj (u : Site 2) (v : Site 2)) :
    (mci_interiorKingGraph Vc).Adj u v := by
  rw [mci_interiorKingGraph, SimpleGraph.induce_adj]
  exact hadj


theorem mci_interiorStepGraph_le_king {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) :
    jil_interiorStepGraph Vc ≤ mci_interiorKingGraph Vc := by
  intro u v hadj
  rw [jil_interiorStepGraph, SimpleGraph.induce_adj] at hadj
  exact mci_interiorKingGraph_axial_adj Vc hadj


theorem mci_offSupport_neighbor_interior {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {z w : Site 2} (hz : z ∈ jil_offSupportInterior Vc)
    (hadj : (hypercubicLattice 2).Adj z w) (hwoff : w ∉ Vc.support) :
    w ∈ jil_offSupportInterior Vc := by
  obtain ⟨hzoff, hzint⟩ := (jil_mem_offSupportInterior Vc _).mp hz
  have hpar := jec_localConstancy Vc hadj hzoff hwoff
  rw [jil_mem_offSupportInterior]
  refine ⟨hwoff, ?_⟩
  rw [jec_mem_leftRegion] at hzint ⊢
  intro h; exact hzint (hpar.mpr h)


theorem mci_offSupport_walk_interior {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (p : (hypercubicLattice 2).Walk x y)
    (hp : ∀ z ∈ p.support, z ∉ Vc.support)
    (hx : x ∈ jil_offSupportInterior Vc) :
    ∀ z ∈ p.support, z ∈ jil_offSupportInterior Vc := by
  induction p with
  | nil =>
    intro z hz
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz; exact hz ▸ hx
  | @cons u v w hadj q ih =>
    have hv : v ∉ Vc.support := hp v (by simp [SimpleGraph.Walk.support_cons])
    have htail : ∀ z ∈ q.support, z ∉ Vc.support := fun z hz =>
      hp z (by rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ hz)
    have hvint : v ∈ jil_offSupportInterior Vc :=
      mci_offSupport_neighbor_interior Vc hx hadj hv
    have ihv := ih htail hvint
    intro z hz
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
    rcases hz with h | h
    · exact h ▸ hx
    · exact ihv z h


theorem mci_diagonal_king_bridge {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) {x y : ℤ}
    (hxy : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
    (hdiag : (![x + 1, y + 1] : Site 2) ∈ jil_offSupportInterior Vc)
    (helb_off : (![x + 1, y] : Site 2) ∉ Vc.support) :
    ∃ helb : (![x + 1, y] : Site 2) ∈ jil_offSupportInterior Vc,
      (mci_interiorKingGraph Vc).Adj ⟨![x, y], hxy⟩ ⟨![x + 1, y], helb⟩ ∧
      (mci_interiorKingGraph Vc).Adj ⟨![x + 1, y], helb⟩ ⟨![x + 1, y + 1], hdiag⟩ := by
  
  have hadj_left : (hypercubicLattice 2).Adj (![x, y] : Site 2) ![x + 1, y] := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
  have helb : (![x + 1, y] : Site 2) ∈ jil_offSupportInterior Vc :=
    mci_offSupport_neighbor_interior Vc hxy hadj_left helb_off
  refine ⟨helb, ?_, ?_⟩
  · exact mci_interiorKingGraph_axial_adj Vc (u := ⟨_, hxy⟩) (v := ⟨_, helb⟩) hadj_left
  · have hadj_up : (hypercubicLattice 2).Adj (![x + 1, y] : Site 2) ![x + 1, y + 1] := by
      rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
    exact mci_interiorKingGraph_axial_adj Vc (u := ⟨_, helb⟩) (v := ⟨_, hdiag⟩) hadj_up


theorem mci_diagonal_king_reachable {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) {x y : ℤ}
    (hxy : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
    (hdiag : (![x + 1, y + 1] : Site 2) ∈ jil_offSupportInterior Vc)
    (helb_off : (![x + 1, y] : Site 2) ∉ Vc.support) :
    (mci_interiorKingGraph Vc).Reachable ⟨![x, y], hxy⟩ ⟨![x + 1, y + 1], hdiag⟩ := by
  obtain ⟨_helb, h1, h2⟩ := mci_diagonal_king_bridge Vc hxy hdiag helb_off
  exact (h1.reachable).trans h2.reachable


theorem mci_kingStepGraph_walk_interior {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : jil_offSupportInterior Vc}
    (w : (mci_interiorKingGraph Vc).Walk x y) :
    ∃ p : mci_kingGraph.Walk (x : Site 2) (y : Site 2),
      ∀ z ∈ p.support, z ∈ jil_offSupportInterior Vc := by
  classical
  induction w with
  | @nil u => exact ⟨SimpleGraph.Walk.nil, by
      intro z hz
      rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
      subst hz; exact u.2⟩
  | @cons u v t hadj q ih =>
    obtain ⟨p, hp⟩ := ih
    have hadj' : mci_kingGraph.Adj (u : Site 2) (v : Site 2) := by
      rw [mci_interiorKingGraph] at hadj
      exact SimpleGraph.induce_adj.mp hadj
    refine ⟨SimpleGraph.Walk.cons hadj' p, ?_⟩
    intro z hz
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
    rcases hz with h | h
    · subst h; exact u.2
    · exact hp z h


end Lattice
end StatMech
