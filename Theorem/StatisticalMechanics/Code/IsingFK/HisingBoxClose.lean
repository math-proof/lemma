/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/HisingBoxClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.Ising.InfiniteVolume.Part9
import Theorem.StatisticalMechanics.Code.Lattice.ClusterContourBijection.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.IsingBoxEncoding.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.MagnetizationCorrespondence
open scoped BigOperators


namespace StatMech

namespace IsingFK

open StatMech.Ising StatMech.FK StatMech.Lattice StatMech.Percolation

variable {d n : ℕ}


theorem hbx_mem_bondFinsetTouch_iff (d n : ℕ) (a b : Site d) :
    s(a, b) ∈ bondFinsetTouch d n ↔
      ((hypercubicLattice d).Adj a b ∧ (a ∈ box d n ∨ b ∈ box d n)) := by
  rw [bondFinsetTouch, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, heq⟩
    rw [bondPairsTouch, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨_, _⟩, hadj, htouch⟩ := hp
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h1; subst h2; exact ⟨hadj, htouch⟩
    · subst h1; subst h2; exact ⟨hadj.symm, htouch.symm⟩
  · rintro ⟨hadj, htouch⟩
    refine ⟨(a, b), ?_, rfl⟩
    rw [bondPairsTouch, Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨?_, ?_⟩, hadj, htouch⟩
    · rw [mem_boxFinset]
      rcases htouch with h | h
      · exact box_subset_succ d n h
      · exact ccb_adj_mem_box_succ hadj.symm h
    · rw [mem_boxFinset]
      rcases htouch with h | h
      · exact ccb_adj_mem_box_succ hadj h
      · exact box_subset_succ d n h


theorem hbx_mem_image_edgeIncl_iff (d m : ℕ) (a b : Site d) :
    s(a, b) ∈ Finset.image (edgeIncl d m) (boxGraph d m).edgeFinset ↔
      (a ∈ box d m ∧ b ∈ box d m ∧ (hypercubicLattice d).Adj a b) := by
  constructor
  · intro h
    rw [Finset.mem_image] at h
    obtain ⟨e, he, heq⟩ := h
    induction e with
    | _ u v =>
      rw [edgeIncl, Sym2.map_mk] at heq
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, boxGraph] at he
      simp only [SimpleGraph.comap_adj] at he
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · subst h1; subst h2; exact ⟨u.2, v.2, he⟩
      · subst h1; subst h2; exact ⟨v.2, u.2, he.symm⟩
  · rintro ⟨ha, hb, hadj⟩
    rw [Finset.mem_image]
    refine ⟨s(⟨a, ha⟩, ⟨b, hb⟩), ?_, ?_⟩
    · rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, boxGraph]
      simp only [SimpleGraph.comap_adj]; exact hadj
    · rw [edgeIncl, Sym2.map_mk]


theorem hbx_touch_subset_image (d n : ℕ) :
    bondFinsetTouch d n ⊆ Finset.image (edgeIncl d (n + 1)) (boxGraph d (n + 1)).edgeFinset := by
  intro e he
  induction e with
  | _ a b =>
    rw [hbx_mem_bondFinsetTouch_iff] at he
    obtain ⟨hadj, htouch⟩ := he
    rw [hbx_mem_image_edgeIncl_iff]
    refine ⟨?_, ?_, hadj⟩
    · rcases htouch with h | h
      · exact box_subset_succ d n h
      · exact ccb_adj_mem_box_succ hadj.symm h
    · rcases htouch with h | h
      · exact ccb_adj_mem_box_succ hadj h
      · exact box_subset_succ d n h


theorem hbx_isingBond_latToBox_eq (d n : ℕ) (τ : {x // x ∈ box d n} → Bool)
    (e : Sym2 (boxVerts d (n + 1))) :
    isingBond (latToBox d n τ) e = bond (glue (plusField d) τ) (edgeIncl d (n + 1) e) := by
  induction e with
  | _ u v =>
    rw [isingBond_mk, edgeIncl, Sym2.map_mk, bond_mk, isingSpin_latToBox, isingSpin_latToBox]


theorem hbx_edge_energy (d n : ℕ) (τ : {x // x ∈ box d n} → Bool) :
    ∑ e ∈ (boxGraph d (n + 1)).edgeFinset, isingBond (latToBox d n τ) e
      = (∑ e ∈ bondFinsetTouch d n, bond (glue (plusField d) τ) e)
        + ((Finset.image (edgeIncl d (n + 1)) (boxGraph d (n + 1)).edgeFinset)
            \ bondFinsetTouch d n).card := by
  have hinj : Set.InjOn (edgeIncl d (n + 1))
      ((boxGraph d (n + 1)).edgeFinset : Set (Sym2 (boxVerts d (n + 1)))) :=
    (edgeIncl_injective d (n + 1)).injOn
  rw [Finset.sum_congr rfl (fun e _ => hbx_isingBond_latToBox_eq d n τ e),
    ← Finset.sum_image hinj (g := edgeIncl d (n + 1)) (f := bond (glue (plusField d) τ)),
    ← Finset.sum_sdiff (hbx_touch_subset_image d n)]
  have hcompl : ∑ e ∈ ((Finset.image (edgeIncl d (n + 1)) (boxGraph d (n + 1)).edgeFinset)
        \ bondFinsetTouch d n), bond (glue (plusField d) τ) e
      = ((Finset.image (edgeIncl d (n + 1)) (boxGraph d (n + 1)).edgeFinset)
          \ bondFinsetTouch d n).card := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro e he
    rw [Finset.mem_sdiff] at he
    obtain ⟨hin, hnotin⟩ := he
    induction e with
    | _ a b =>
      rw [hbx_mem_image_edgeIncl_iff] at hin
      obtain ⟨_, _, hadj⟩ := hin
      rw [hbx_mem_bondFinsetTouch_iff, not_and_or, not_or] at hnotin
      have hna : a ∉ box d n := by
        rcases hnotin with h | h
        · exact absurd hadj h
        · exact h.1
      have hnb : b ∉ box d n := by
        rcases hnotin with h | h
        · exact absurd hadj h
        · exact h.2
      rw [bond_mk, spin_true _ (by rw [glue_not_mem _ _ hna]; rfl),
        spin_true _ (by rw [glue_not_mem _ _ hnb]; rfl), Nat.cast_one]; ring
  rw [hcompl]; ring


end IsingFK
end StatMech
