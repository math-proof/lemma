/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalEdgeDegreeHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightRootCutHallEquivalence
open Finset
open scoped symmDiff


namespace StatMech.FrontierA

variable {A B : Type*} [Fintype A] [Fintype B]


theorem card_le_bipartiteNeighbors_of_edgeDegree
    (r : A -> B -> Prop) [DecidableRel r]
    (S : Finset A)
    (hne : ∀ a ∈ S, (Finset.univ.filter (r a)).Nonempty)
    (hdeg : ∀ a ∈ S, ∀ b, r a b ->
      (Finset.univ.filter fun x => r x b).card <=
        (Finset.univ.filter (r a)).card) :
    S.card <= (Finset.univ.filter fun b => ∃ a ∈ S, r a b).card := by
  let LA : A -> Finset B := fun a => Finset.univ.filter (r a)
  let RB : B -> Finset A := fun b => Finset.univ.filter fun a => r a b
  let N : Finset B := Finset.univ.filter fun b => ∃ a ∈ S, r a b
  have hLApos : ∀ a ∈ S, 0 < (LA a).card := by
    intro a ha
    exact Finset.card_pos.mpr (hne a ha)
  have hRBpos : ∀ a ∈ S, ∀ b ∈ LA a, 0 < (RB b).card := by
    intro a ha b hb
    rw [Finset.card_pos]
    refine ⟨a, ?_⟩
    simpa [LA, RB] using hb
  have hLAN : ∀ a ∈ S, LA a ⊆ N := by
    intro a ha b hb
    simp only [N, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨a, ha, by simpa [LA] using hb⟩
  have hleft : (S.card : ℚ) =
      ∑ a ∈ S, ∑ b ∈ LA a, (1 : ℚ) / (LA a).card := by
    calc
      (S.card : ℚ) = ∑ a ∈ S, (1 : ℚ) := by simp
      _ = ∑ a ∈ S, ∑ b ∈ LA a, (1 : ℚ) / (LA a).card := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.sum_const, nsmul_eq_mul]
        norm_num [Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hLApos a ha))]
  have hstep : (∑ a ∈ S, ∑ b ∈ LA a,
        (1 : ℚ) / (LA a).card) <=
      ∑ a ∈ S, ∑ b ∈ LA a, (1 : ℚ) / (RB b).card := by
    apply Finset.sum_le_sum
    intro a ha
    apply Finset.sum_le_sum
    intro b hb
    apply one_div_le_one_div_of_le
    · exact_mod_cast hRBpos a ha b hb
    · exact_mod_cast hdeg a ha b (by simpa [LA] using hb)
  have hreindex : (∑ a ∈ S, ∑ b ∈ LA a,
        (1 : ℚ) / (RB b).card) =
      ∑ b ∈ N, ∑ a ∈ S,
        if r a b then (1 : ℚ) / (RB b).card else 0 := by
    calc
      _ = ∑ a ∈ S, ∑ b ∈ N,
          if r a b then (1 : ℚ) / (RB b).card else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [← Finset.sum_filter]
        have hfilter : N.filter (r a) = LA a := by
          ext b
          simp only [N, LA, Finset.mem_filter, Finset.mem_univ,
            true_and]
          constructor
          · exact fun h => h.2
          · exact fun hab => ⟨⟨a, ha, hab⟩, hab⟩
        rw [hfilter]
      _ = _ := by rw [Finset.sum_comm]
  have hright : (∑ b ∈ N, ∑ a ∈ S,
        if r a b then (1 : ℚ) / (RB b).card else 0) <=
      (N.card : ℚ) := by
    calc
      _ <= ∑ b ∈ N, (1 : ℚ) := by
        apply Finset.sum_le_sum
        intro b hb
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        have hsub : (S.filter fun a => r a b).card <= (RB b).card := by
          apply Finset.card_le_card
          intro a ha
          simp only [Finset.mem_filter] at ha
          simp [RB, ha.2]
        have hpos : 0 < (RB b).card := by
          simp only [N, Finset.mem_filter, Finset.mem_univ, true_and] at hb
          obtain ⟨a, haS, hab⟩ := hb
          exact hRBpos a haS b (by simp [LA, hab])
        rw [div_eq_mul_inv]
        simp only [one_mul]
        have hcast : ((S.filter fun a => r a b).card : ℚ) <=
            ((RB b).card : ℚ) := by exact_mod_cast hsub
        have hinv : 0 <= (((RB b).card : ℚ)⁻¹) := by positivity
        calc
          ((S.filter fun a => r a b).card : ℚ) *
              ((RB b).card : ℚ)⁻¹ <=
            ((RB b).card : ℚ) * ((RB b).card : ℚ)⁻¹ :=
              mul_le_mul_of_nonneg_right hcast hinv
          _ = 1 := by field_simp
      _ = (N.card : ℚ) := by simp
  have hrat : (S.card : ℚ) <= (N.card : ℚ) := by
    rw [hleft]
    exact hstep.trans (hreindex.le.trans hright)
  exact_mod_cast hrat


theorem tightBipartiteNeighborhood_collisionSurplus
    (r : A -> B -> Prop) [DecidableRel r]
    (S : Finset A)
    (N : Finset B)
    (hN : N = Finset.univ.filter fun b => ∃ a ∈ S, r a b)
    (htight : N.card + 1 = S.card) :
    (∑ b ∈ N, ((S.filter fun a => r a b).card : ℤ)) - N.card =
      (∑ a ∈ S, ((Finset.univ.filter (r a)).card : ℤ)) - S.card + 1 := by
  have hfilter : ∀ a ∈ S, N.filter (r a) = Finset.univ.filter (r a) := by
    intro a ha
    ext b
    simp only [hN, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · exact fun hab => ⟨⟨a, ha, hab⟩, hab⟩
  have hedge := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    r (s := S) (t := N)
  simp only [Finset.bipartiteAbove, Finset.bipartiteBelow] at hedge
  have hedgeNat : (∑ a ∈ S,
      (Finset.univ.filter (r a)).card) =
      ∑ b ∈ N, (S.filter fun a => r a b).card := by
    calc
      _ = ∑ a ∈ S, (N.filter (r a)).card := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hfilter a ha]
      _ = _ := hedge
  have hedge' : (∑ a ∈ S,
      ((Finset.univ.filter (r a)).card : ℤ)) =
      ∑ b ∈ N, ((S.filter fun a => r a b).card : ℤ) := by
    exact_mod_cast hedgeNat
  omega


theorem bipartiteNeighborhood_collisionSurplus
    (r : A -> B -> Prop) [DecidableRel r]
    (S : Finset A)
    (N : Finset B)
    (hN : N = Finset.univ.filter fun b => ∃ a ∈ S, r a b) :
    (∑ b ∈ N, ((S.filter fun a => r a b).card : ℤ)) - N.card =
      (∑ a ∈ S, ((Finset.univ.filter (r a)).card : ℤ)) - S.card +
        ((S.card : ℤ) - N.card) := by
  have hfilter : ∀ a ∈ S, N.filter (r a) =
      Finset.univ.filter (r a) := by
    intro a ha
    ext b
    simp only [hN, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · exact fun hab => ⟨⟨a, ha, hab⟩, hab⟩
  have hedge := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    r (s := S) (t := N)
  simp only [Finset.bipartiteAbove, Finset.bipartiteBelow] at hedge
  have hedgeNat : (∑ a ∈ S,
      (Finset.univ.filter (r a)).card) =
      ∑ b ∈ N, (S.filter fun a => r a b).card := by
    calc
      _ = ∑ a ∈ S, (N.filter (r a)).card := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hfilter a ha]
      _ = _ := hedge
  have hedge' : (∑ a ∈ S,
      ((Finset.univ.filter (r a)).card : ℤ)) =
      ∑ b ∈ N, ((S.filter fun a => r a b).card : ℤ) := by
    exact_mod_cast hedgeNat
  omega


theorem card_le_bipartiteNeighbors_of_collisionSurplus
    (r : A -> B -> Prop) [DecidableRel r]
    (S : Finset A)
    (N : Finset B)
    (hN : N = Finset.univ.filter fun b => ∃ a ∈ S, r a b)
    (hsurplus :
      (∑ b ∈ N, ((S.filter fun a => r a b).card : ℤ)) - N.card ≤
        (∑ a ∈ S, ((Finset.univ.filter (r a)).card : ℤ)) - S.card) :
    S.card ≤ N.card := by
  have hid := bipartiteNeighborhood_collisionSurplus r S N hN
  omega


theorem bipartiteNeighborhood_collisionSurplus_iff_card_le
    (r : A -> B -> Prop) [DecidableRel r]
    (S : Finset A)
    (N : Finset B)
    (hN : N = Finset.univ.filter fun b => ∃ a ∈ S, r a b) :
    ((∑ b ∈ N, ((S.filter fun a => r a b).card : ℤ)) - N.card ≤
        (∑ a ∈ S, ((Finset.univ.filter (r a)).card : ℤ)) - S.card) ↔
      S.card ≤ N.card := by
  have hid := bipartiteNeighborhood_collisionSurplus r S N hN
  omega


end StatMech.FrontierA
