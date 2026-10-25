/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SingleLeafHallClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.ForestLeafCountClose.Part4
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem slh_cut_neighbor {W : Type*} [DecidableEq W] {G : SimpleGraph W} {x a : W} (hxa : x ≠ a)
    (h : G.Reachable x a) :
    ∃ (c : W) (hc : c ≠ x) (ha : a ≠ x), G.Adj x c ∧
      (G.induce ({x}ᶜ : Set W)).Reachable ⟨c, by simpa using hc⟩ ⟨a, by simpa using ha⟩ := by
  classical
  obtain ⟨p⟩ := h
  set q : G.Walk x a := (p.toPath : G.Walk x a) with hq
  have hqp : q.IsPath := (p.toPath).2
  have hnnil : ¬ q.Nil := Walk.not_nil_of_ne hxa
  set c := q.snd with hc
  have hadj : G.Adj x c := q.adj_snd hnnil
  have hcx : c ≠ x := (G.ne_of_adj hadj).symm
  have hax : a ≠ x := fun h => hxa h.symm
  have hsupp : ∀ y ∈ q.tail.support, y ∈ ({x}ᶜ : Set W) := by
    intro y hy
    have hcons : q.support = x :: q.tail.support := by
      rw [Walk.support_tail_of_not_nil q hnnil, Walk.cons_tail_support]
    have hnd := hqp.support_nodup
    rw [hcons, List.nodup_cons] at hnd
    intro hyx
    simp only [Set.mem_singleton_iff] at hyx
    subst hyx
    exact hnd.1 hy
  have hind := q.tail.induce ({x}ᶜ : Set W) hsupp
  exact ⟨c, hcx, hax, hadj, ⟨hind.copy (by simp [hc]) rfl⟩⟩


theorem slh_deg_ge_three_of_cut {W : Type*} [DecidableEq W] [Fintype W] {G : SimpleGraph W}
    [DecidableRel G.Adj] {x a₁ a₂ a₃ : W}
    (hr₁ : G.Reachable x a₁) (hr₂ : G.Reachable x a₂) (hr₃ : G.Reachable x a₃)
    (hx₁ : x ≠ a₁) (hx₂ : x ≠ a₂) (hx₃ : x ≠ a₃)
    (hcut₁₂ : ¬ (G.induce ({x}ᶜ : Set W)).Reachable
      ⟨a₁, by simpa using hx₁.symm⟩ ⟨a₂, by simpa using hx₂.symm⟩)
    (hcut₁₃ : ¬ (G.induce ({x}ᶜ : Set W)).Reachable
      ⟨a₁, by simpa using hx₁.symm⟩ ⟨a₃, by simpa using hx₃.symm⟩)
    (hcut₂₃ : ¬ (G.induce ({x}ᶜ : Set W)).Reachable
      ⟨a₂, by simpa using hx₂.symm⟩ ⟨a₃, by simpa using hx₃.symm⟩) :
    3 ≤ G.degree x := by
  classical
  obtain ⟨c₁, _, _, hadj₁, hreach₁⟩ := slh_cut_neighbor hx₁ hr₁
  obtain ⟨c₂, _, _, hadj₂, hreach₂⟩ := slh_cut_neighbor hx₂ hr₂
  obtain ⟨c₃, _, _, hadj₃, hreach₃⟩ := slh_cut_neighbor hx₃ hr₃
  have h12 : c₁ ≠ c₂ := by rintro rfl; exact hcut₁₂ (hreach₁.symm.trans hreach₂)
  have h13 : c₁ ≠ c₃ := by rintro rfl; exact hcut₁₃ (hreach₁.symm.trans hreach₃)
  have h23 : c₂ ≠ c₃ := by rintro rfl; exact hcut₂₃ (hreach₂.symm.trans hreach₃)
  have hsub : ({c₁, c₂, c₃} : Finset W) ⊆ G.neighborFinset x := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rw [G.mem_neighborFinset]
    rcases hw with rfl | rfl | rfl
    · exact hadj₁
    · exact hadj₂
    · exact hadj₃
  have hcard : ({c₁, c₂, c₃} : Finset W).card = 3 :=
    Finset.card_eq_three.mpr ⟨c₁, c₂, c₃, h12, h13, h23, rfl⟩
  calc 3 = ({c₁, c₂, c₃} : Finset W).card := hcard.symm
    _ ≤ (G.neighborFinset x).card := Finset.card_le_card hsub
    _ = G.degree x := G.card_neighborFinset_eq_degree x


theorem slh_edge_transfer (x u v : Site d) (ω : ConfigSpace (Sym2 (Site d)))
    (hadj : (openSubgraph d ω).Adj u v) (hux : u ≠ x) (hvx : v ≠ x) :
    (openSubgraph d (removeSite x ω)).Adj u v := by
  obtain ⟨hl, ho⟩ := hadj
  refine ⟨hl, ?_⟩
  rw [removeSite_apply_of_notMem]
  · exact ho
  · intro hx
    rw [Sym2.mem_iff] at hx
    rcases hx with rfl | rfl
    · exact hux rfl
    · exact hvx rfl


theorem slh_walk_avoid_transfer {x u v : Site d} {ω : ConfigSpace (Sym2 (Site d))}
    (w : (openSubgraph d ω).Walk u v) (hw : x ∉ w.support) :
    (openSubgraph d (removeSite x ω)).Reachable u v := by
  induction w with
  | nil => exact Reachable.refl _
  | @cons a b c hab w ih =>
    rw [Walk.support_cons, List.mem_cons, not_or] at hw
    obtain ⟨hax, hw'⟩ := hw
    have hbx : x ≠ b := fun h => by subst h; exact hw' (w.start_mem_support)
    exact (Adj.reachable
      (slh_edge_transfer x a b ω hab (Ne.symm hax) (Ne.symm hbx))).trans (ih hw')


theorem slh_connected_removeSite_of_G_induce {W : Type*} {ω : ConfigSpace (Sym2 (Site d))}
    {G : SimpleGraph W} (π : W → Site d)
    (hπ : ∀ u v, G.Adj u v → (openSubgraph d ω).Adj (π u) (π v))
    (hπinj : Function.Injective π)
    {p wi wj : W} (hwi : wi ≠ p) (hwj : wj ≠ p)
    (h : (G.induce ({p}ᶜ : Set W)).Reachable ⟨wi, by simpa using hwi⟩ ⟨wj, by simpa using hwj⟩) :
    Connected d (removeSite (π p) ω) (π wi) (π wj) := by
  obtain ⟨w⟩ := h
  set f : (G.induce ({p}ᶜ : Set W)) →g (openSubgraph d ω) :=
    { toFun := fun u => π u.1
      map_rel' := fun {a b} hab => hπ a.1 b.1 hab } with hf
  set w' := w.map f with hw'
  have hsupp : (π p) ∉ w'.support := by
    intro hx
    rw [hw', Walk.support_map, List.mem_map] at hx
    obtain ⟨⟨c, hc⟩, _, hcx⟩ := hx
    rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hc
    exact hc (hπinj (by simpa [hf] using hcx))
  exact slh_walk_avoid_transfer w' hsupp


end Percolation
end StatMech
