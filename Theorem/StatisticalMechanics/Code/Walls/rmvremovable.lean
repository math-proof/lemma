/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmvremovable.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.EarExistence.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Theorem.StatisticalMechanics.Code.Walls.fbcconnected.Part4
import Theorem.StatisticalMechanics.Code.Walls.atcattachstep.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc_leafremoval.Part2
import Theorem.StatisticalMechanics.Code.Walls.nbcnoncut.Part2
import Theorem.StatisticalMechanics.Code.Walls.earremovable.Part5
open Finset Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable


theorem rmv_reroute_reachable {V : Type*} (G : SimpleGraph V) (c w : V) (hwc : w ≠ c)
    (hhub : ∀ z, G.Adj c z → z ≠ w → G.Adj w z) :
    ∀ (n : ℕ) {x : V} (hx : x ≠ c) (p : G.Walk x w), p.length = n →
      (G.induce ({c}ᶜ : Set V)).Reachable ⟨x, hx⟩ ⟨w, hwc⟩ := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro x hx p hlen
    cases p with
    | nil => exact Reachable.refl _
    | @cons _ b _ hab q =>
      
      by_cases hbc : b = c
      · 
        have hxc_adj : G.Adj x c := hbc ▸ hab
        by_cases hxw : x = w
        · 
          have : (⟨x, hx⟩ : ↑({c}ᶜ : Set V)) = ⟨w, hwc⟩ := Subtype.ext hxw
          rw [this]
        · have hwx : G.Adj w x := hhub x hxc_adj.symm hxw
          have hstep : (G.induce ({c}ᶜ : Set V)).Adj ⟨x, hx⟩ ⟨w, hwc⟩ := by
            rw [SimpleGraph.induce_adj]; exact hwx.symm
          exact hstep.reachable
      · 
        have hstep : (G.induce ({c}ᶜ : Set V)).Adj ⟨x, hx⟩ ⟨b, hbc⟩ := by
          rw [SimpleGraph.induce_adj]; exact hab
        have hqlen : q.length < n := by
          simp only [SimpleGraph.Walk.length_cons] at hlen; omega
        exact hstep.reachable.trans (IH q.length hqlen hbc q rfl)


theorem rmv_noncut_of_common_neighbour {K : Set (Site 2)} (hconn : CellConnected K)
    {c w : Site 2} (hc : c ∈ K) (hw : w ∈ K) (hwc : w ≠ c)
    (hhub : ∀ z ∈ K, (hypercubicLattice 2).Adj c z → z ≠ w → (hypercubicLattice 2).Adj w z) :
    CellConnected (K \ {c}) := by
  classical
  set G := (hypercubicLattice 2).induce K with hG
  
  set cv : ↥K := ⟨c, hc⟩ with hcv
  set wv : ↥K := ⟨w, hw⟩ with hwv
  have hwvcv : wv ≠ cv := by
    intro h; exact hwc (congrArg Subtype.val h)
  
  have hhubG : ∀ zv : ↥K, G.Adj cv zv → zv ≠ wv → G.Adj wv zv := by
    intro zv hadj hne
    rw [hG, SimpleGraph.induce_adj] at hadj ⊢
    refine hhub zv.1 zv.2 hadj ?_
    intro h; exact hne (Subtype.ext h)
  
  apply cellConnected_diff_of_iso K c hc
  
  have hwvmem : wv ∈ ({cv}ᶜ : Set ↥K) := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact hwvcv
  haveI : Nonempty ↥({cv}ᶜ : Set ↥K) := ⟨⟨wv, hwvmem⟩⟩
  refine SimpleGraph.Connected.mk ?_
  
  · have reach : ∀ t : ↥({cv}ᶜ : Set ↥K),
        (G.induce ({cv}ᶜ : Set ↥K)).Reachable ⟨wv, hwvmem⟩ t := by
      intro t
      obtain ⟨tv, htv⟩ := t
      have htvc : tv ≠ cv := by
        intro h; rw [Set.mem_compl_iff, Set.mem_singleton_iff] at htv; exact htv h
      
      obtain ⟨p⟩ := hconn.preconnected tv wv
      
      have hr := rmv_reroute_reachable G cv wv hwvcv hhubG p.length htvc p rfl
      
      have e1 : (⟨wv, hwvmem⟩ : ↥({cv}ᶜ : Set ↥K)) = ⟨wv, hwvcv⟩ := rfl
      have e2 : (⟨tv, htv⟩ : ↥({cv}ᶜ : Set ↥K)) = ⟨tv, htvc⟩ := rfl
      rw [e1, e2]; exact hr.symm
    intro u v
    exact (reach u).symm.trans (reach v)


theorem rmv_adj_diag_leftCell (c : Site 2) :
    (hypercubicLattice 2).Adj (c + ![-1, -1]) (ear_leftCell c) := by
  rw [ear_leftCell, hypercubicLattice_adj, Fin.sum_univ_two]
  simp only [Pi.add_apply]
  norm_num


theorem rmv_adj_diag_downCell (c : Site 2) :
    (hypercubicLattice 2).Adj (c + ![-1, -1]) (ear_downCell c) := by
  rw [ear_downCell, hypercubicLattice_adj, Fin.sum_univ_two]
  simp only [Pi.add_apply]
  norm_num


theorem rmv_diag_ne (c : Site 2) : c + ![-1, -1] ≠ c := by
  intro h; have := congrFun h 0; simp [Pi.add_apply] at this


theorem rmv_extreme_diag_noncut {K : Set (Site 2)} (hconn : CellConnected K) {c : Site 2}
    (hc : ear_IsGlobalExtreme K c) (hdiag : c + ![-1, -1] ∈ K) :
    CellConnected (K \ {c}) := by
  refine rmv_noncut_of_common_neighbour hconn hc.mem hdiag (rmv_diag_ne c) ?_
  intro z hzK hadj _
  
  rcases ear_globalExtreme_neighbor_leftCell_or_downCell K c z hc hzK hadj with h | h
  · rw [h]; exact rmv_adj_diag_leftCell c
  · rw [h]; exact rmv_adj_diag_downCell c


theorem rmv_extreme_diag_removable {K : Finset (Site 2)}
    (hconn : IsConnectedCluster K) {c : Site 2}
    (hc : ear_IsGlobalExtreme (↑K : Set (Site 2)) c) (hcorigin : c ≠ origin 2)
    (hdiag : c + ![-1, -1] ∈ (↑K : Set (Site 2))) :
    ∃ d ∈ K, d ≠ origin 2 ∧ (∃ n ∉ K, (hypercubicLattice 2).Adj d n) ∧
      CellConnected ((↑K : Set (Site 2)) \ {d}) := by
  refine ⟨c, by exact_mod_cast hc.mem, hcorigin,
    ear_globalExtreme_boundary (↑K : Set (Site 2)) c hc, ?_⟩
  exact rmv_extreme_diag_noncut (nbc_cellConnected_of_isConnectedCluster hconn) hc hdiag


theorem rmv_extreme_dichotomy {K : Finset (Site 2)} (hcard : 2 ≤ K.card)
    (hconn : IsConnectedCluster K) {c : Site 2}
    (hc : ear_IsGlobalExtreme (↑K : Set (Site 2)) c) (hcorigin : c ≠ origin 2) :
    (∃ d ∈ K, d ≠ origin 2 ∧ (∃ n ∉ K, (hypercubicLattice 2).Adj d n) ∧
        CellConnected ((↑K : Set (Site 2)) \ {d}))
      ∨ (ear_leftCell c ∈ (↑K : Set (Site 2)) ∧ ear_downCell c ∈ (↑K : Set (Site 2)) ∧
          c + ![-1, -1] ∉ (↑K : Set (Site 2))) := by
  classical
  
  rcases ear_globalExtreme_dichotomy hcard hconn hc hcorigin with hrem | ⟨hp, hq⟩
  · exact Or.inl hrem
  · 
    by_cases hdiag : c + ![-1, -1] ∈ (↑K : Set (Site 2))
    · exact Or.inl (rmv_extreme_diag_removable hconn hc hcorigin hdiag)
    · exact Or.inr ⟨hp, hq, hdiag⟩


end Walls
end StatMech
