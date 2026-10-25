/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedInteractionCore.Part4
import Instance.StatisticalMechanics.Code.FrontierD.FKRectRefinedIntersection
open scoped BigOperators
open Finset


namespace StatMech.FrontierD

open StatMech.Onsager

open IntegralSquareTorusCycle

noncomputable section

variable {L : Nat} [Fact (8 < L)]

theorem pointMass_mul_sum (a b : ZMod L × ZMod L) :
    (∑ p, pointMass a p * pointMass b p) =
      if a = b then 1 else 0 := by
  classical
  by_cases h : a = b
  · subst b
    simp [pointMass]
  · have hs : ¬ b = a := fun hba => h hba.symm
    simp [pointMass, h, hs]

theorem pointMass_west_normalized
    (a p : ZMod L × ZMod L) :
    pointMass a (-1 + p.1, p.2) =
      pointMass (a.1 + 1, a.2) p := by
  convert pointMass_west a p using 1 <;> ring

theorem pointMass_south_normalized
    (a p : ZMod L × ZMod L) :
    pointMass a (p.1, -1 + p.2) =
      pointMass (a.1, a.2 + 1) p := by
  convert pointMass_south a p using 1 <;> ring

theorem zmod_two_ne_zero : (2 : ZMod L) ≠ 0 := by
  change ((2 : Nat) : ZMod L) ≠ 0
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hdvd
  have hle := Nat.le_of_dvd (by norm_num : 0 < 2) hdvd
  have hL := (Fact.out : 8 < L)
  omega

theorem zmod_three_ne_zero : (3 : ZMod L) ≠ 0 := by
  change ((3 : Nat) : ZMod L) ≠ 0
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hdvd
  have hle := Nat.le_of_dvd (by norm_num : 0 < 3) hdvd
  have hL := (Fact.out : 8 < L)
  omega


theorem fkRectRefined_horizontal_west_interaction (x y : ZMod L) :
    fkRectRefinedRawInteraction
        [((x - 1, y - 1), 1), ((x - 1, y), 1)]
        [((x + 2, y), 2), ((x + 1, y), 2), ((x, y), 2),
          ((x - 1, y), 2)] = 1 := by
  classical
  unfold fkRectRefinedRawInteraction
  simp only [dartHorizontal, dartVertical, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Fin.isValue, Fin.reduceEq,
    ↓reduceIte, add_zero, if_false, if_true, neg_zero, zero_mul, mul_zero]
  ring_nf
  have h2 := zmod_two_ne_zero (L := L)
  have h3 := zmod_three_ne_zero (L := L)
  have hm12 : (2 : ZMod L) ≠ -1 := by
    intro h
    apply h3
    calc
      (3 : ZMod L) = 2 - (-1) := by ring
      _ = 0 := by rw [h]; ring
  have hm11 : (1 : ZMod L) ≠ -1 := by
    intro h
    apply h2
    calc
      (2 : ZMod L) = 1 + 1 := by ring
      _ = (-1) + 1 := congrArg (fun z : ZMod L => z + 1) h
      _ = 0 := by ring
  repeat' rw [Finset.sum_add_distrib]
  simp_rw [pointMass_west_normalized]
  simp_rw [pointMass_mul_sum]
  have ha : ¬ (-1 + x = 1 + x + 1) := by
    intro h
    apply h3
    calc
      (3 : ZMod L) = (1 + x + 1) - (-1 + x) := by ring
      _ = 0 := by rw [h]; ring
  have hb : ¬ (-1 + x = x + 1) := by
    intro h
    apply h2
    calc
      (2 : ZMod L) = (x + 1) - (-1 + x) := by ring
      _ = 0 := by rw [h]; ring
  have hc : -1 + x = -2 + x + 1 := by ring
  have hn : (-2 : ZMod L) ≠ 1 := by
    intro h
    apply h3
    calc
      (3 : ZMod L) = 1 - (-2) := by ring
      _ = 0 := by rw [h]; ring
  simp [ha, hb, hc, hn, h2]


theorem fkRectRefined_horizontal_east_interaction (x y : ZMod L) :
    fkRectRefinedRawInteraction
        [((x + 1, y + 1), 3), ((x + 1, y), 3)]
        [((x + 2, y), 2), ((x + 1, y), 2), ((x, y), 2),
          ((x - 1, y), 2)] = -1 := by
  classical
  unfold fkRectRefinedRawInteraction
  simp only [dartHorizontal, dartVertical, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Fin.isValue, Fin.reduceEq,
    ↓reduceIte, add_zero, if_false, if_true, neg_zero, zero_mul, mul_zero]
  ring_nf
  have h1 : (1 : ZMod L) ≠ 0 := one_ne_zero
  have h2 := zmod_two_ne_zero (L := L)
  have h3 := zmod_three_ne_zero (L := L)
  simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  repeat' rw [Finset.sum_add_distrib]
  simp_rw [pointMass_west_normalized]
  simp_rw [pointMass_mul_sum]
  have ha : ¬ (x + 1 = 1 + x + 1) := by
    intro h
    apply h1
    calc
      (1 : ZMod L) = (1 + x + 1) - (x + 1) := by ring
      _ = 0 := by rw [h]; ring
  have hb : 1 + x = x + 1 := by ring
  have hc : ¬ (1 + x = -2 + x + 1) := by
    intro h
    apply h2
    calc
      (2 : ZMod L) = (1 + x) - (-2 + x + 1) := by ring
      _ = 0 := by rw [h]; ring
  simp [ha, hb, hc, h1, h2, h3]


theorem fkRectRefined_vertical_west_interaction (x y : ZMod L) :
    fkRectRefinedRawInteraction
        [((x - 1, y - 1), 0), ((x, y - 1), 0)]
        [((x, y - 2), 1), ((x, y - 1), 1), ((x, y), 1),
          ((x, y + 1), 1)] = 1 := by
  classical
  unfold fkRectRefinedRawInteraction
  simp only [dartHorizontal, dartVertical, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Fin.isValue, Fin.reduceEq,
    ↓reduceIte, add_zero, if_false, if_true, neg_zero, zero_mul, mul_zero]
  ring_nf
  repeat' rw [Finset.sum_add_distrib]
  simp_rw [pointMass_south_normalized]
  simp_rw [pointMass_mul_sum]
  have h1 : (1 : ZMod L) ≠ 0 := one_ne_zero
  have h2 := zmod_two_ne_zero (L := L)
  have h3 := zmod_three_ne_zero (L := L)
  have hm11 : (-1 : ZMod L) ≠ 1 := by
    intro h
    apply h2
    calc
      (2 : ZMod L) = 1 - (-1) := by ring
      _ = 0 := by rw [h]; ring
  have hm12 : (-1 : ZMod L) ≠ 2 := by
    intro h
    apply h3
    calc
      (3 : ZMod L) = 2 - (-1) := by ring
      _ = 0 := by rw [h]; ring
  ring_nf
  simp [h1, h2, h3, hm11, hm12]


theorem fkRectRefined_vertical_east_interaction (x y : ZMod L) :
    fkRectRefinedRawInteraction
        [((x + 1, y + 1), 2), ((x, y + 1), 2)]
        [((x, y - 2), 1), ((x, y - 1), 1), ((x, y), 1),
          ((x, y + 1), 1)] = -1 := by
  classical
  unfold fkRectRefinedRawInteraction
  simp only [dartHorizontal, dartVertical, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Fin.isValue, Fin.reduceEq,
    ↓reduceIte, add_zero, if_false, if_true, neg_zero, zero_mul, mul_zero]
  ring_nf
  simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  repeat' rw [Finset.sum_add_distrib]
  simp_rw [pointMass_south_normalized]
  simp_rw [pointMass_mul_sum]
  have h1 : (1 : ZMod L) ≠ 0 := one_ne_zero
  have h2 := zmod_two_ne_zero (L := L)
  have h3 := zmod_three_ne_zero (L := L)
  have hm11 : (1 : ZMod L) ≠ -1 := by
    intro h
    apply h2
    calc
      (2 : ZMod L) = 1 - (-1) := by ring
      _ = 0 := by rw [← h]; ring
  have h12 : (1 : ZMod L) ≠ 2 := by
    intro h
    apply h1
    calc
      (1 : ZMod L) = 2 - 1 := by ring
      _ = 0 := by rw [← h]; ring
  ring_nf
  simp [h1, h2, h3, hm11, h12]


end
end StatMech.FrontierD
