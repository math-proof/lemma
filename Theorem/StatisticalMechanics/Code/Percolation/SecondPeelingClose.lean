/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SecondPeelingClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.SingleLeafHallClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BoundaryPruningClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BKSpanningTreeClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.OpenSpanningForestClose.Part4
import Def.StatisticalMechanics.Code.Percolation.SecondPeelingClose
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem spc_survivor_has_neighbor {V : Type*} (T : SimpleGraph V) (B : Set V)
    (v : V) (h : spc_OnBPath T B v) : ∃ w, T.Adj v w ∧ spc_OnBPath T B w := by
  obtain ⟨b₁, b₂, hb₁, hb₂, hne, p, hp, hmem⟩ := h
  rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hmem
  obtain ⟨i, hvi, hile⟩ := hmem
  have hlen : 0 < p.length := by
    rcases Nat.eq_zero_or_pos p.length with h0 | h0
    · exact absurd (p.eq_of_length_eq_zero h0) hne
    · exact h0
  by_cases hi : i < p.length
  · exact ⟨p.getVert (i + 1), hvi ▸ p.adj_getVert_succ hi,
      ⟨b₁, b₂, hb₁, hb₂, hne, p, hp, p.getVert_mem_support _⟩⟩
  · have hieq : i = p.length := le_antisymm hile (not_lt.mp hi)
    refine ⟨p.getVert (p.length - 1), ?_,
      ⟨b₁, b₂, hb₁, hb₂, hne, p, hp, p.getVert_mem_support _⟩⟩
    have hadj := p.adj_getVert_succ (i := p.length - 1) (by omega)
    rw [Nat.sub_add_cancel hlen] at hadj
    rw [← hvi, hieq]; exact hadj.symm


theorem spc_interior_two_neighbors {V : Type*} (T : SimpleGraph V) (B : Set V)
    (v : V) (hv : spc_OnBPath T B v) (hvB : v ∉ B) :
    ∃ w₁ w₂ : V, w₁ ≠ w₂ ∧ T.Adj v w₁ ∧ T.Adj v w₂ ∧
      spc_OnBPath T B w₁ ∧ spc_OnBPath T B w₂ := by
  obtain ⟨b₁, b₂, hb₁, hb₂, hne, p, hp, hmem⟩ := hv
  rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hmem
  obtain ⟨i, hvi, hile⟩ := hmem
  have hvb1 : v ≠ b₁ := fun h => hvB (h ▸ hb₁)
  have hvb2 : v ≠ b₂ := fun h => hvB (h ▸ hb₂)
  have hi0 : i ≠ 0 := by intro h; subst h; rw [p.getVert_zero] at hvi; exact hvb1 hvi.symm
  have hilen : i ≠ p.length := by
    intro h; subst h; rw [p.getVert_length] at hvi; exact hvb2 hvi.symm
  have hipos : 0 < i := Nat.pos_of_ne_zero hi0
  have hilt : i < p.length := lt_of_le_of_ne hile hilen
  refine ⟨p.getVert (i - 1), p.getVert (i + 1), ?_, ?_, ?_, ?_, ?_⟩
  · intro hcontra
    have := hp.getVert_injOn (x₁ := i - 1) (x₂ := i + 1)
      (by simp only [Set.mem_setOf_eq]; omega) (by simp only [Set.mem_setOf_eq]; omega) hcontra
    omega
  · rw [← hvi]
    have hadj := p.adj_getVert_succ (i := i - 1) (by omega)
    rw [Nat.sub_add_cancel hipos] at hadj; exact hadj.symm
  · rw [← hvi]; exact p.adj_getVert_succ hilt
  · exact ⟨b₁, b₂, hb₁, hb₂, hne, p, hp, p.getVert_mem_support _⟩
  · exact ⟨b₁, b₂, hb₁, hb₂, hne, p, hp, p.getVert_mem_support _⟩


section Degrees

variable {W : Type*} [Fintype W] [DecidableEq W] (F : SimpleGraph W) [DecidableRel F.Adj]

omit [DecidableEq W] in

theorem spc_deg_ge_one (v w : W) (h : F.Adj v w) : 1 ≤ F.degree v := by
  rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, F.degree_pos_iff_exists_adj]; exact ⟨w, h⟩

set_option linter.unusedDecidableInType false in

theorem spc_deg_ge_two (v w₁ w₂ : W) (hne : w₁ ≠ w₂) (h1 : F.Adj v w₁) (h2 : F.Adj v w₂) :
    2 ≤ F.degree v := by
  rw [← F.card_neighborFinset_eq_degree]
  have hsub : ({w₁, w₂} : Finset W) ⊆ F.neighborFinset v := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> rw [mem_neighborFinset] <;> assumption
  calc (2 : ℕ) = ({w₁, w₂} : Finset W).card := (Finset.card_pair hne).symm
    _ ≤ _ := Finset.card_le_card hsub

set_option linter.unusedDecidableInType false in

theorem spc_deg_ge_three (v w₁ w₂ w₃ : W) (h12 : w₁ ≠ w₂) (h13 : w₁ ≠ w₃) (h23 : w₂ ≠ w₃)
    (h1 : F.Adj v w₁) (h2 : F.Adj v w₂) (h3 : F.Adj v w₃) : 3 ≤ F.degree v := by
  rw [← F.card_neighborFinset_eq_degree]
  have hsub : ({w₁, w₂, w₃} : Finset W) ⊆ F.neighborFinset v := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> rw [mem_neighborFinset] <;> assumption
  calc (3 : ℕ) = ({w₁, w₂, w₃} : Finset W).card := by
        rw [Finset.card_insert_of_notMem (by simp [h12, h13]), Finset.card_pair h23]
    _ ≤ _ := Finset.card_le_card hsub

end Degrees


theorem spc_map_acyclic {V V' : Type*} {G : SimpleGraph V} (hac : G.IsAcyclic) (f : V ↪ V') :
    (SimpleGraph.map f G).IsAcyclic := by
  classical
  rcases isEmpty_or_nonempty V with hV | hV
  · have hbot : SimpleGraph.map f G = ⊥ := by
      ext x y; rw [SimpleGraph.map_adj]; simp only [bot_adj, iff_false]
      rintro ⟨a, _, _, _, _⟩; exact isEmptyElim a
    rw [hbot]; exact isAcyclic_bot
  obtain ⟨g, hg⟩ : ∃ g : V' → V, ∀ a, g (f a) = a :=
    ⟨Function.invFun f, Function.leftInverse_invFun f.injective⟩
  set gHom : (SimpleGraph.map f G) →g G :=
    ⟨g, by intro x y hxy; rw [SimpleGraph.map_adj] at hxy
           obtain ⟨a, b, hab, rfl, rfl⟩ := hxy; rw [hg, hg]; exact hab⟩ with hgHom
  have hgHom_apply : ∀ w, gHom w = g w := fun _ => rfl
  intro u c hc
  have hlen : 0 < c.length := by have := hc.three_le_length; omega
  
  have hsupp_mem : ∀ w ∈ c.support, ∃ a, f a = w := by
    intro w hw
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hw
    obtain ⟨i, hi, hil⟩ := hw
    rcases Nat.lt_or_ge i c.length with hlt | hge
    · have hadj := c.adj_getVert_succ hlt
      rw [SimpleGraph.map_adj] at hadj; obtain ⟨a, b, hab, h1, h2⟩ := hadj
      exact ⟨a, h1.trans hi⟩
    · have hieq : i = c.length := le_antisymm hil hge
      have hadj := c.adj_getVert_succ (i := c.length - 1) (by omega)
      rw [SimpleGraph.map_adj] at hadj; obtain ⟨a, b, hab, h1, h2⟩ := hadj
      refine ⟨b, ?_⟩; rw [h2, ← hi, hieq]; congr 1; omega
  
  have hginj : ∀ x ∈ c.support, ∀ y ∈ c.support, g x = g y → x = y := by
    intro x hx y hy hxy
    obtain ⟨ax, rfl⟩ := hsupp_mem x hx
    obtain ⟨ay, rfl⟩ := hsupp_mem y hy
    rw [hg, hg] at hxy; rw [hxy]
  
  refine hac (c.map gHom) ⟨⟨⟨?_⟩, ?_⟩, ?_⟩
  · rw [SimpleGraph.Walk.edges_map]
    refine List.Nodup.map_on ?_ hc.edges_nodup
    intro e1 he1 e2 he2 heq
    induction e1 with
    | _ p q =>
      induction e2 with
      | _ r s =>
        simp only [Sym2.map_mk, Sym2.eq_iff] at heq
        have hp := c.fst_mem_support_of_mem_edges he1
        have hq := c.snd_mem_support_of_mem_edges he1
        have hr := c.fst_mem_support_of_mem_edges he2
        have hs := c.snd_mem_support_of_mem_edges he2
        rw [Sym2.eq_iff]
        rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨hginj p hp r hr h1, hginj q hq s hs h2⟩
        · exact Or.inr ⟨hginj p hp s hs h1, hginj q hq r hr h2⟩
  · intro hnil
    have hl := SimpleGraph.Walk.length_map gHom c
    rw [hnil] at hl; simp only [SimpleGraph.Walk.length_nil] at hl; omega
  · rw [SimpleGraph.Walk.support_map]
    have htail : (List.map (⇑gHom) c.support).tail = List.map (⇑gHom) c.support.tail := by
      cases c.support <;> simp
    rw [htail]
    refine List.Nodup.map_on ?_ hc.support_nodup
    intro x hx y hy
    simp only [hgHom_apply]
    exact fun h => hginj x (List.mem_of_mem_tail hx) y (List.mem_of_mem_tail hy) h


end Percolation
end StatMech
