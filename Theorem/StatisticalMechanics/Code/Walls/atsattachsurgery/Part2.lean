/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/atsattachsurgery.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsSingleCircuit.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsBoundaryConnected.Part4
import Theorem.StatisticalMechanics.Code.Walls.pc2boundaryconn.Part4
import Theorem.StatisticalMechanics.Code.Walls.fbcconnected.Part4
import Def.StatisticalMechanics.Code.Walls.atsattachsurgery
open Finset Set SimpleGraph


namespace StatMech

namespace Walls

open StatMech.Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable


theorem ats_sharedPrimalEdge_corners_of_f {f g : Site 2}
    (hadj : (hypercubicLattice 2).Adj f g) :
    ∃ u v : Site 2, sharedPrimalEdge f g = s(u, v) ∧
      (u = ![f 0, f 1] ∨ u = ![f 0 + 1, f 1] ∨ u = ![f 0 + 1, f 1 + 1] ∨ u = ![f 0, f 1 + 1]) ∧
      (v = ![f 0, f 1] ∨ v = ![f 0 + 1, f 1] ∨ v = ![f 0 + 1, f 1 + 1] ∨ v = ![f 0, f 1 + 1]) := by
  classical
  have hfeq : f = ![f 0, f 1] := by funext i; fin_cases i <;> rfl
  have hgeq : g = ![g 0, g 1] := by funext i; fin_cases i <;> rfl
  
  have hd := hadj
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hd
  
  by_cases h0 : f 0 = g 0
  · 
    have h1 : (f 1 - g 1).natAbs = 1 := by
      have : (f 0 - g 0).natAbs = 0 := by omega
      omega
    rcases Int.natAbs_eq_iff.mp h1 with he | he <;> simp only [Nat.cast_one] at he
    · 
      have hg : g = ![f 0, f 1 - 1] := by
        rw [hgeq]; rw [site2_eq]; exact ⟨h0.symm, by omega⟩
      subst hg
      have h := sharedPrimalEdge_bottom (f 0) (f 1)
      rw [show (![f 0, f 1] : Site 2) = f from hfeq.symm] at h
      refine ⟨_, _, h, ?_, ?_⟩
      · unfold faceCorner00; left; rfl
      · unfold faceCorner10; right; left; rfl
    · 
      have hg : g = ![f 0, f 1 + 1] := by
        rw [hgeq]; rw [site2_eq]; exact ⟨h0.symm, by omega⟩
      subst hg
      have h := sharedPrimalEdge_top (f 0) (f 1)
      rw [show (![f 0, f 1] : Site 2) = f from hfeq.symm] at h
      refine ⟨_, _, h, ?_, ?_⟩
      · unfold faceCorner01; right; right; right; rfl
      · unfold faceCorner11; right; right; left; rfl
  · 
    have hf1 : f 1 = g 1 := by
      have hb : (f 0 - g 0).natAbs ≥ 1 := by
        rcases Int.natAbs_eq (f 0 - g 0) with hh | hh <;> omega
      by_contra hne
      have : (f 1 - g 1).natAbs ≥ 1 := by
        rcases Int.natAbs_eq (f 1 - g 1) with hh | hh <;> omega
      omega
    have h0abs : (f 0 - g 0).natAbs = 1 := by
      have : (f 1 - g 1).natAbs = 0 := by omega
      omega
    rcases Int.natAbs_eq_iff.mp h0abs with he | he <;> simp only [Nat.cast_one] at he
    · 
      have hg : g = ![f 0 - 1, f 1] := by
        rw [hgeq]; rw [site2_eq]; exact ⟨by omega, hf1.symm⟩
      subst hg
      have h := sharedPrimalEdge_left (f 0) (f 1)
      rw [show (![f 0, f 1] : Site 2) = f from hfeq.symm] at h
      refine ⟨_, _, h, ?_, ?_⟩
      · unfold faceCorner00; left; rfl
      · unfold faceCorner01; right; right; right; rfl
    · 
      have hg : g = ![f 0 + 1, f 1] := by
        rw [hgeq]; rw [site2_eq]; exact ⟨by omega, hf1.symm⟩
      subst hg
      have h := sharedPrimalEdge_right (f 0) (f 1)
      rw [show (![f 0, f 1] : Site 2) = f from hfeq.symm] at h
      refine ⟨_, _, h, ?_, ?_⟩
      · unfold faceCorner10; right; left; rfl
      · unfold faceCorner11; right; right; left; rfl


theorem ats_adj_insert_iff_of_notCorner {K : Finset (Site 2)} {c f g : Site 2}
    (hadj : (hypercubicLattice 2).Adj f g) (hc : ¬ ats_faceHasCorner c f) :
    (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Adj f g ↔
      (faceBoundaryGraph (↑K : Set (Site 2))).Adj f g := by
  obtain ⟨u, v, hshared, hu, hv⟩ := ats_sharedPrimalEdge_corners_of_f hadj
  unfold ats_faceHasCorner at hc
  push Not at hc
  apply ats_adj_insert_of_shared_avoid hshared
  · rcases hu with rfl | rfl | rfl | rfl
    · exact fun h => hc.1 h.symm
    · exact fun h => hc.2.1 h.symm
    · exact fun h => hc.2.2.1 h.symm
    · exact fun h => hc.2.2.2 h.symm
  · rcases hv with rfl | rfl | rfl | rfl
    · exact fun h => hc.1 h.symm
    · exact fun h => hc.2.1 h.symm
    · exact fun h => hc.2.2.1 h.symm
    · exact fun h => hc.2.2.2 h.symm


theorem ats_walk_transfer_of_avoid {K : Finset (Site 2)} {c a b : Site 2}
    (p : (faceBoundaryGraph (↑K : Set (Site 2))).Walk a b)
    (havoid : ∀ w ∈ p.support, ¬ ats_faceHasCorner c w) :
    ∃ q : (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Walk a b,
      q.support = p.support := by
  induction p with
  | nil => exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | @cons x y z hxy q ih =>
    have hx : ¬ ats_faceHasCorner c x := havoid x (by
      rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_self)
    have htail : ∀ w ∈ q.support, ¬ ats_faceHasCorner c w := by
      intro w hw
      exact havoid w (by rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ hw)
    obtain ⟨q', hq'⟩ := ih htail
    have hxy' : (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Adj x y :=
      (ats_adj_insert_iff_of_notCorner hxy.1 hx).mpr hxy
    refine ⟨SimpleGraph.Walk.cons hxy' q', ?_⟩
    rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_cons, hq']


theorem ats_walk_transfer_of_avoid' {K : Finset (Site 2)} {c a b : Site 2}
    (p : (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Walk a b)
    (havoid : ∀ w ∈ p.support, ¬ ats_faceHasCorner c w) :
    ∃ q : (faceBoundaryGraph (↑K : Set (Site 2))).Walk a b,
      q.support = p.support := by
  induction p with
  | nil => exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | @cons x y z hxy q ih =>
    have hx : ¬ ats_faceHasCorner c x := havoid x (by
      rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_self)
    have htail : ∀ w ∈ q.support, ¬ ats_faceHasCorner c w := by
      intro w hw
      exact havoid w (by rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ hw)
    obtain ⟨q', hq'⟩ := ih htail
    have hxy' : (faceBoundaryGraph (↑K : Set (Site 2))).Adj x y :=
      (ats_adj_insert_iff_of_notCorner hxy.1 hx).mp hxy
    refine ⟨SimpleGraph.Walk.cons hxy' q', ?_⟩
    rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_cons, hq']


theorem ats_reachable_insert_of_avoidWalk {K : Finset (Site 2)} {c a b : Site 2}
    (p : (faceBoundaryGraph (↑K : Set (Site 2))).Walk a b)
    (havoid : ∀ w ∈ p.support, ¬ ats_faceHasCorner c w) :
    (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Reachable a b :=
  let ⟨q, _⟩ := ats_walk_transfer_of_avoid p havoid
  ⟨q⟩


theorem ats_mem_support_insert_iff_of_notCorner {K : Finset (Site 2)} {c f : Site 2}
    (hc : ¬ ats_faceHasCorner c f) :
    f ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support ↔
      f ∈ (faceBoundaryGraph (↑K : Set (Site 2))).support := by
  rw [SimpleGraph.mem_support, SimpleGraph.mem_support]
  constructor
  · rintro ⟨g, hg⟩; exact ⟨g, (ats_adj_insert_iff_of_notCorner hg.1 hc).mp hg⟩
  · rintro ⟨g, hg⟩; exact ⟨g, (ats_adj_insert_iff_of_notCorner hg.1 hc).mpr hg⟩


end Walls
end StatMech
