/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc19menger.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.bc18mengerhard.Part3
import Def.StatisticalMechanics.Code.Walls.bc19menger.Part4


namespace StatMech.Walls

open SimpleGraph

universe u

variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} {k : ℕ}


theorem bc19_directSolution [Fintype V] {A B Y : Set V} {x y : V}
    (hxy : G.Adj x y) (hxY : x ∉ Y) (hyY : y ∉ Y)
    (hxA : x ∈ A) (hyB : y ∈ B) (hYA : Y ⊆ A) (hYB : Y ⊆ B)
    (hk : Y.ncard + 1 = k) :
    Nonempty (bc16_DisjointPathFamily G A B (Fin k)) := by
  obtain ⟨f, hinj, hf⟩ := bc17_exists_finInj_of_le_ncard (Set.toFinite Y) (le_refl Y.ncard)
  have F := bc19_directSum hxy f hf hinj hxY hyY hxA hyB hYA hYB
  refine ⟨bc19_reindex ?_ F⟩
  rw [← hk]; exact (bc19_sumEquiv Y.ncard).symm


theorem bc19_Y_sep_of_xyA {A B Y : Set V} {x y : V}
    (hxY : x ∉ Y) (hyY : y ∉ Y) (hxA : x ∈ A) (hyA : y ∈ A)
    (hYsep : bc16_IsSeparator (G.deleteEdges {s(x, y)}) A B Y) :
    bc16_IsSeparator G A B Y := by
  by_contra hnot
  rw [bc16_IsSeparator] at hnot
  push Not at hnot
  obtain ⟨a₀, ha₀, b₀, hb₀, R₀, hR₀⟩ := hnot
  have ha₀Y : a₀ ∉ Y := fun h => hR₀ a₀ h R₀.start_mem_support
  have hR₀restr : (bc17_restr G {v | v ∉ Y}).Reachable a₀ b₀ :=
    ⟨bc18_walkToRestrCompl R₀ (fun w hw hwY => hR₀ w hwY hw)⟩
  rcases hR₀restr with ⟨R₀'⟩
  rcases bc18_splitAtEdge (x := x) (y := y) R₀' with hkeep | ⟨_, h2⟩ | ⟨_, h2⟩
  · rw [bc18_restr_compl_deleteEdges] at hkeep
    exact bc18_contra_of_reachable hYsep ha₀ hb₀ ha₀Y hkeep
  · rw [bc18_restr_compl_deleteEdges] at h2
    exact bc18_contra_of_reachable hYsep hyA hb₀ hyY h2
  · rw [bc18_restr_compl_deleteEdges] at h2
    exact bc18_contra_of_reachable hYsep hxA hb₀ hxY h2


theorem bc19_subset_AReach_of_min [Fintype V] {A B S : Set V}
    (hSsep : bc16_IsSeparator G A B S)
    (hmin : ∀ C, bc16_IsSeparator G A B C → k ≤ C.ncard)
    (hScard : S.ncard = k) : S ⊆ bc18_AReach G A S :=
  fun s hsS => bc18_mem_AReach_of_essential hSsep (bc19_essential hmin hScard hsS)


theorem bc19_getAFan [Fintype V] {N : ℕ} {A B S : Set V}
    (IH : ∀ (G' : SimpleGraph V), G'.edgeSet.ncard < N → ∀ (A' B' : Set V), bc17_HardDir G' A' B')
    (hltN : (bc17_restr G (bc18_AReach G A S)).edgeSet.ncard < G.edgeSet.ncard →
            (bc17_restr G (bc18_AReach G A S)).edgeSet.ncard < N)
    (hmin : ∀ C, bc16_IsSeparator G A B C → k ≤ C.ncard)
    (hSsep : bc16_IsSeparator G A B S) (hScard : S.ncard = k)
    (hcase : S ⊆ A ∨ ¬ S ⊆ B) :
    ∃ RA : Set V, RA ⊆ bc18_AReach G A S ∧ Nonempty (bc19_AFan G A S RA k) := by
  by_cases hSA : S ⊆ A
  · exact ⟨S, bc19_subset_AReach_of_min hSsep hmin hScard, bc19_trivFan (B := A) hScard hSA⟩
  · have hSB : ¬ S ⊆ B := hcase.resolve_left hSA
    exact ⟨bc18_AReach G A S, le_refl _,
      bc19_aFan_extract hmin hSsep
        (IH _ (hltN (bc19_Aside_strict_of_notSubsetB hSsep hmin hScard hSB)) A S)⟩


theorem bc19_routeS [Fintype V] {N : ℕ} {A B S : Set V}
    (IH : ∀ (G' : SimpleGraph V), G'.edgeSet.ncard < N → ∀ (A' B' : Set V), bc17_HardDir G' A' B')
    (hltA : (bc17_restr G (bc18_AReach G A S)).edgeSet.ncard < G.edgeSet.ncard →
            (bc17_restr G (bc18_AReach G A S)).edgeSet.ncard < N)
    (hltB : (bc17_restr G (bc18_AReach G B S)).edgeSet.ncard < G.edgeSet.ncard →
            (bc17_restr G (bc18_AReach G B S)).edgeSet.ncard < N)
    (hmin : ∀ C, bc16_IsSeparator G A B C → k ≤ C.ncard)
    (hSsep : bc16_IsSeparator G A B S) (hScard : S.ncard = k)
    (hcA : S ⊆ A ∨ ¬ S ⊆ B) (hcB : S ⊆ B ∨ ¬ S ⊆ A) :
    Nonempty (bc16_DisjointPathFamily G A B (Fin k)) := by
  obtain ⟨RA, hRA, FA⟩ := bc19_getAFan IH hltA hmin hSsep hScard hcA
  obtain ⟨RB, hRB, FB⟩ := bc19_getAFan (A := B) (B := A) IH hltB
    (fun C hC => hmin C (bc16_separator_symm hC)) (bc16_separator_symm hSsep) hScard hcB
  exact ⟨bc19_glueFans hScard
    (fun z ⟨hzA, hzB⟩ => bc18_AReach_inter_subset hSsep ⟨hRA hzA, hRB hzB⟩) FA.some FB.some⟩


theorem bc19_hardDir_aux [Fintype V] (N : ℕ) :
    ∀ (G : SimpleGraph V), G.edgeSet.ncard < N → ∀ (A B : Set V), bc17_HardDir G A B := by
  induction N with
  | zero => intro G hlt; exact absurd hlt (by omega)
  | succ N IH =>
    intro G hlt A B k hmin
    by_cases hbot : G = ⊥
    · subst hbot; exact bc17_hard_bot A B hmin
    · have hne : G.edgeSet.ncard ≠ 0 := by
        intro h0; apply hbot
        rw [← edgeSet_eq_empty, ← Set.ncard_eq_zero (Set.toFinite _)]; exact h0
      obtain ⟨x, y, hxy⟩ : ∃ x y, G.Adj x y := by
        by_contra hc; push Not at hc
        apply hne; rw [Set.ncard_eq_zero (Set.toFinite _)]
        ext e; obtain ⟨u, v⟩ := e
        simp only [mem_edgeSet, Set.mem_empty_iff_false, iff_false]; exact hc u v
      have hdel_lt : (G.deleteEdges {s(x, y)}).edgeSet.ncard < N := by
        have := bc17_edgeSet_ncard_lt_of_deleteEdge (G := G) hxy; omega
      rcases bc17_deleteEdge_dichotomy hxy hmin with hC1 | hC2
      · 
        exact bc17_hardDir_step_case1 (IH _ hdel_lt A B) hC1
      · 
        obtain ⟨Y, hYsep, hYlt, hxY, hyY, hSxsep, hSysep⟩ := hC2
        have hYnotG : ¬ bc16_IsSeparator G A B Y :=
          fun hG => absurd (hmin Y hG) (by omega)
        have hSxcard : (insert x Y).ncard = k := by
          have hge := hmin _ hSxsep
          rw [Set.ncard_insert_of_notMem hxY (Set.toFinite Y)] at hge ⊢; omega
        have hSycard : (insert y Y).ncard = k := by
          have hge := hmin _ hSysep
          rw [Set.ncard_insert_of_notMem hyY (Set.toFinite Y)] at hge ⊢; omega
        have hYcard1 : Y.ncard + 1 = k := by
          have := hmin _ hSxsep
          rw [Set.ncard_insert_of_notMem hxY (Set.toFinite Y)] at this; omega
        have mkLtA : ∀ S : Set V,
            (bc17_restr G (bc18_AReach G A S)).edgeSet.ncard < G.edgeSet.ncard →
            (bc17_restr G (bc18_AReach G A S)).edgeSet.ncard < N := fun S h => by omega
        have mkLtB : ∀ S : Set V,
            (bc17_restr G (bc18_AReach G B S)).edgeSet.ncard < G.edgeSet.ncard →
            (bc17_restr G (bc18_AReach G B S)).edgeSet.ncard < N := fun S h => by omega
        have hnotxyA : ¬ (x ∈ A ∧ y ∈ A) := fun ⟨hxA, hyA⟩ =>
          hYnotG (bc19_Y_sep_of_xyA hxY hyY hxA hyA hYsep)
        have hnotxyB : ¬ (x ∈ B ∧ y ∈ B) := fun ⟨hxB, hyB⟩ =>
          hYnotG (bc16_separator_symm
            (bc19_Y_sep_of_xyA (B := A) hxY hyY hxB hyB (bc16_separator_symm hYsep)))
        by_cases hSxA : insert x Y ⊆ A <;> by_cases hSxB : insert x Y ⊆ B
        · exact bc19_routeS IH (mkLtA _) (mkLtB _) hmin hSxsep hSxcard
            (Or.inl hSxA) (Or.inl hSxB)
        · by_cases hSyA : insert y Y ⊆ A <;> by_cases hSyB : insert y Y ⊆ B
          · exact bc19_routeS IH (mkLtA _) (mkLtB _) hmin hSysep hSycard
              (Or.inl hSyA) (Or.inl hSyB)
          · exact absurd ⟨hSxA (Set.mem_insert _ _), hSyA (Set.mem_insert _ _)⟩ hnotxyA
          · refine bc19_directSolution hxy hxY hyY
              (hSxA (Set.mem_insert _ _)) (hSyB (Set.mem_insert _ _))
              (fun z hz => hSxA (Set.mem_insert_of_mem _ hz))
              (fun z hz => hSyB (Set.mem_insert_of_mem _ hz)) hYcard1
          · exact bc19_routeS IH (mkLtA _) (mkLtB _) hmin hSysep hSycard
              (Or.inr hSyB) (Or.inr hSyA)
        · by_cases hSyA : insert y Y ⊆ A <;> by_cases hSyB : insert y Y ⊆ B
          · exact bc19_routeS IH (mkLtA _) (mkLtB _) hmin hSysep hSycard
              (Or.inl hSyA) (Or.inl hSyB)
          · refine bc19_directSolution hxy.symm hyY hxY
              (hSyA (Set.mem_insert _ _)) (hSxB (Set.mem_insert _ _))
              (fun z hz => hSyA (Set.mem_insert_of_mem _ hz))
              (fun z hz => hSxB (Set.mem_insert_of_mem _ hz)) hYcard1
          · exact absurd ⟨hSxB (Set.mem_insert _ _), hSyB (Set.mem_insert _ _)⟩ hnotxyB
          · exact bc19_routeS IH (mkLtA _) (mkLtB _) hmin hSysep hSycard
              (Or.inr hSyB) (Or.inr hSyA)
        · exact bc19_routeS IH (mkLtA _) (mkLtB _) hmin hSxsep hSxcard
            (Or.inr hSxB) (Or.inr hSxA)


theorem bc19_hardDir_all [Fintype V] (G : SimpleGraph V) (A B : Set V) :
    bc17_HardDir G A B :=
  bc19_hardDir_aux (G.edgeSet.ncard + 1) G (by omega) A B


theorem bc19_menger_minmax [Fintype V] (G : SimpleGraph V) (A B : Set V) {k : ℕ}
    (hmin : ∀ C, bc16_IsSeparator G A B C → k ≤ C.ncard) :
    ∃ F : bc16_DisjointPathFamily G A B (Fin k),
      ∀ C, bc16_IsSeparator G A B C → Fintype.card (Fin k) ≤ C.ncard := by
  obtain ⟨F⟩ := bc19_hardDir_all G A B k hmin
  exact ⟨F, fun C hC => by simpa using hmin C hC⟩

end StatMech.Walls
