/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalEdgeDegreeHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightRootCutHallEquivalence
import Def.StatisticalMechanics.Code.FrontierA.GrahamCanonicalEdgeDegreeHall.Part2
open Finset
open scoped symmDiff


namespace StatMech.FrontierA

variable {A B : Type*} [Fintype A] [Fintype B]


theorem card_le_bipartiteNeighbors_of_collisionTokenEmbedding
    [DecidableEq A] [DecidableEq B]
    (r : A -> B -> Prop) [DecidableRel r]
    (S : Finset A)
    (N : Finset B)
    (hN : N = Finset.univ.filter fun b => ∃ a ∈ S, r a b)
    (hemb : BipartiteCollisionTokenEmbedding r S N) :
    S.card ≤ N.card := by
  classical
  obtain ⟨leftBase, rightBase, hleft, hright, ⟨f⟩⟩ := hemb
  have hleftMem (a : ↑S) :
      leftBase a ∈ Finset.univ.filter (r a.1) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hleft a
  have hrightMem (b : ↑N) :
      rightBase b ∈ S.filter fun a => r a b.1 := by
    exact Finset.mem_filter.mpr (hright b)
  have hleftCard : Fintype.card
      (bipartiteLeftSurplusToken r S leftBase) + S.card =
      ∑ a ∈ S, (Finset.univ.filter (r a)).card := by
    calc
      _ = (∑ a : ↑S,
            ((Finset.univ.filter (r a.1)).card - 1)) + S.card := by
        congr 1
        calc
          _ = ∑ a : ↑S, Fintype.card
              ↑((Finset.univ.filter (r a.1)).erase (leftBase a)) :=
            Fintype.card_sigma
          _ = _ := by
            apply Finset.sum_congr rfl
            intro a _
            rw [Fintype.card_coe,
              Finset.card_erase_of_mem (hleftMem a)]
      _ = (∑ a : ↑S,
            ((Finset.univ.filter (r a.1)).card - 1)) +
          ∑ _a : ↑S, 1 := by simp
      _ = ∑ a : ↑S,
          (((Finset.univ.filter (r a.1)).card - 1) + 1) := by
        rw [Finset.sum_add_distrib]
      _ = ∑ a : ↑S, (Finset.univ.filter (r a.1)).card := by
        apply Finset.sum_congr rfl
        intro a _
        have hpos := Finset.card_pos.mpr ⟨leftBase a, hleftMem a⟩
        omega
      _ = _ := Finset.sum_coe_sort S
        (fun a => (Finset.univ.filter (r a)).card)
  have hrightCard : Fintype.card
      (bipartiteRightCollisionToken r S N rightBase) + N.card =
      ∑ b ∈ N, (S.filter fun a => r a b).card := by
    calc
      _ = (∑ b : ↑N,
            ((S.filter fun a => r a b.1).card - 1)) + N.card := by
        congr 1
        calc
          _ = ∑ b : ↑N, Fintype.card
              ↑((S.filter fun a => r a b.1).erase (rightBase b)) :=
            Fintype.card_sigma
          _ = _ := by
            apply Finset.sum_congr rfl
            intro b _
            rw [Fintype.card_coe,
              Finset.card_erase_of_mem (hrightMem b)]
      _ = (∑ b : ↑N,
            ((S.filter fun a => r a b.1).card - 1)) +
          ∑ _b : ↑N, 1 := by simp
      _ = ∑ b : ↑N,
          (((S.filter fun a => r a b.1).card - 1) + 1) := by
        rw [Finset.sum_add_distrib]
      _ = ∑ b : ↑N, (S.filter fun a => r a b.1).card := by
        apply Finset.sum_congr rfl
        intro b _
        have hpos := Finset.card_pos.mpr ⟨rightBase b, hrightMem b⟩
        omega
      _ = _ := Finset.sum_coe_sort N
        (fun b => (S.filter fun a => r a b).card)
  have htoken := Fintype.card_le_of_embedding f
  have hedge := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    r (s := S) (t := N)
  simp only [Finset.bipartiteAbove, Finset.bipartiteBelow] at hedge
  have hfilter : ∀ a ∈ S, N.filter (r a) =
      Finset.univ.filter (r a) := by
    intro a ha
    ext b
    simp only [hN, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · exact fun hab => ⟨⟨a, ha, hab⟩, hab⟩
  have hedge' : (∑ a ∈ S, (Finset.univ.filter (r a)).card) =
      ∑ b ∈ N, (S.filter fun a => r a b).card := by
    calc
      _ = ∑ a ∈ S, (N.filter (r a)).card := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hfilter a ha]
      _ = _ := hedge
  omega

end StatMech.FrontierA
