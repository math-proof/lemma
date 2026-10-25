/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Abbrev.StatisticalMechanics.Code.Universality.ScratchTwoChannelScaleOneMaskHall.Part7


namespace StatMech.Universality

theorem rlcScaleOneFailure_route_not_open
    (rho : RlcScaleOneConnectorFailure) {mask : Nat}
    (hmask : mask ∈ rlcScaleOneRouteMasks) :
    ¬RlcScaleOneRouteOpen rho.1 mask := by
  intro hopen
  exact rho.2 ⟨mask, hmask, hopen⟩

theorem rlcScaleOne_exists_closed_edge_of_route_not_open
    (omega : RlcScaleOneEdgeConfig) (mask : Nat)
    (h : ¬RlcScaleOneRouteOpen omega mask) :
    ∃ i : Fin 16, mask.testBit i ∧ omega i = false := by
  by_contra hex
  push Not at hex
  apply h
  intro i hi
  have hne := hex i hi
  cases homega : omega i <;> simp_all

theorem rlcScaleOneFailure_closed_edge
    (rho : RlcScaleOneConnectorFailure) {mask : Nat}
    (hmask : mask ∈ rlcScaleOneRouteMasks) :
    ∃ i : Fin 16, mask.testBit i ∧ rho.1 i = false :=
  rlcScaleOne_exists_closed_edge_of_route_not_open rho.1 mask
    (rlcScaleOneFailure_route_not_open rho hmask)

theorem rlcScaleOneMask384_support (i : Fin 16) (h : Nat.testBit 384 i) :
    i = 7 ∨ i = 8 := by revert i; decide

theorem rlcScaleOneMask19_support (i : Fin 16) (h : Nat.testBit 19 i) :
    i = 0 ∨ i = 1 ∨ i = 4 := by revert i; decide

theorem rlcScaleOneMask7168_support (i : Fin 16) (h : Nat.testBit 7168 i) :
    i = 10 ∨ i = 11 ∨ i = 12 := by revert i; decide

theorem rlcScaleOneMask28_support (i : Fin 16) (h : Nat.testBit 28 i) :
    i = 2 ∨ i = 3 ∨ i = 4 := by revert i; decide

theorem rlcScaleOneMask50176_support (i : Fin 16) (h : Nat.testBit 50176 i) :
    i = 10 ∨ i = 14 ∨ i = 15 := by revert i; decide

theorem rlcScaleOneMask8960_support (i : Fin 16) (h : Nat.testBit 8960 i) :
    i = 8 ∨ i = 9 ∨ i = 13 := by revert i; decide

theorem rlcScaleOneMask13312_support (i : Fin 16) (h : Nat.testBit 13312 i) :
    i = 10 ∨ i = 12 ∨ i = 13 := by revert i; decide

theorem rlcScaleOneMask8800_support (i : Fin 16) (h : Nat.testBit 8800 i) :
    i = 5 ∨ i = 6 ∨ i = 9 ∨ i = 13 := by revert i; decide

theorem rlcScaleOneMask56_support (i : Fin 16) (h : Nat.testBit 56 i) :
    i = 3 ∨ i = 4 ∨ i = 5 := by revert i; decide

theorem rlcScaleOneMask344_support (i : Fin 16) (h : Nat.testBit 344 i) :
    i = 3 ∨ i = 4 ∨ i = 6 ∨ i = 8 := by revert i; decide

theorem rlcScaleOneMask224_support (i : Fin 16) (h : Nat.testBit 224 i) :
    i = 5 ∨ i = 6 ∨ i = 7 := by revert i; decide

theorem rlcScaleOneMask196_support (i : Fin 16) (h : Nat.testBit 196 i) :
    i = 2 ∨ i = 6 ∨ i = 7 := by revert i; decide

theorem rlcScaleOneMask2816_support (i : Fin 16) (h : Nat.testBit 2816 i) :
    i = 8 ∨ i = 9 ∨ i = 11 := by revert i; decide

theorem rlcScaleOneMask2628_support (i : Fin 16) (h : Nat.testBit 2628 i) :
    i = 2 ∨ i = 6 ∨ i = 9 ∨ i = 11 := by revert i; decide

theorem rlcScaleOneMask2656_support (i : Fin 16) (h : Nat.testBit 2656 i) :
    i = 5 ∨ i = 6 ∨ i = 9 ∨ i = 11 := by revert i; decide

theorem rlcScaleOneFailure_closed384 (rho : RlcScaleOneConnectorFailure) :
    rho.1 7 = false ∨ rho.1 8 = false := by
  rcases rlcScaleOneFailure_closed_edge rho (mask := 384) (by decide) with ⟨i, hi, hc⟩
  rcases rlcScaleOneMask384_support i hi with rfl | rfl
  · exact Or.inl hc
  · exact Or.inr hc

theorem rlcScaleOneFailure_closed19 (rho : RlcScaleOneConnectorFailure) :
    (rho.1 0 = false ∨ rho.1 1 = false) ∨ rho.1 4 = false := by
  rcases rlcScaleOneFailure_closed_edge rho (mask := 19) (by decide) with ⟨i, hi, hc⟩
  rcases rlcScaleOneMask19_support i hi with rfl | rfl | rfl
  · exact Or.inl (Or.inl hc)
  · exact Or.inl (Or.inr hc)
  · exact Or.inr hc

theorem rlcScaleOneFailure_closed7168 (rho : RlcScaleOneConnectorFailure) :
    (rho.1 10 = false ∨ rho.1 11 = false) ∨ rho.1 12 = false := by
  rcases rlcScaleOneFailure_closed_edge rho (mask := 7168) (by decide) with ⟨i, hi, hc⟩
  rcases rlcScaleOneMask7168_support i hi with rfl | rfl | rfl
  · exact Or.inl (Or.inl hc)
  · exact Or.inl (Or.inr hc)
  · exact Or.inr hc

theorem rlcScaleOneFailure_closed28 (rho : RlcScaleOneConnectorFailure) :
    (rho.1 2 = false ∨ rho.1 3 = false) ∨ rho.1 4 = false := by
  rcases rlcScaleOneFailure_closed_edge rho (mask := 28) (by decide) with ⟨i, hi, hc⟩
  rcases rlcScaleOneMask28_support i hi with rfl | rfl | rfl
  · exact Or.inl (Or.inl hc)
  · exact Or.inl (Or.inr hc)
  · exact Or.inr hc

theorem rlcScaleOneFailure_closed50176 (rho : RlcScaleOneConnectorFailure) :
    (rho.1 10 = false ∨ rho.1 14 = false) ∨ rho.1 15 = false := by
  rcases rlcScaleOneFailure_closed_edge rho (mask := 50176) (by decide) with ⟨i, hi, hc⟩
  rcases rlcScaleOneMask50176_support i hi with rfl | rfl | rfl
  · exact Or.inl (Or.inl hc)
  · exact Or.inl (Or.inr hc)
  · exact Or.inr hc

theorem rlcScaleOneFailure_closed8960 (rho : RlcScaleOneConnectorFailure) :
    (rho.1 8 = false ∨ rho.1 9 = false) ∨ rho.1 13 = false := by
  rcases rlcScaleOneFailure_closed_edge rho (mask := 8960) (by decide) with ⟨i, hi, hc⟩
  rcases rlcScaleOneMask8960_support i hi with rfl | rfl | rfl
  · exact Or.inl (Or.inl hc)
  · exact Or.inl (Or.inr hc)
  · exact Or.inr hc

theorem rlcScaleOneFailure_closed13312 (rho : RlcScaleOneConnectorFailure) :
    (rho.1 10 = false ∨ rho.1 12 = false) ∨ rho.1 13 = false := by
  rcases rlcScaleOneFailure_closed_edge rho (mask := 13312) (by decide) with ⟨i, hi, hc⟩
  rcases rlcScaleOneMask13312_support i hi with rfl | rfl | rfl
  · exact Or.inl (Or.inl hc)
  · exact Or.inl (Or.inr hc)
  · exact Or.inr hc

theorem rlcScaleOneFailure_closed8800 (rho : RlcScaleOneConnectorFailure) :
    ((rho.1 5 = false ∨ rho.1 6 = false) ∨ rho.1 9 = false) ∨
      rho.1 13 = false := by
  rcases rlcScaleOneFailure_closed_edge rho (mask := 8800) (by decide) with ⟨i, hi, hc⟩
  rcases rlcScaleOneMask8800_support i hi with rfl | rfl | rfl | rfl
  · exact Or.inl (Or.inl (Or.inl hc))
  · exact Or.inl (Or.inl (Or.inr hc))
  · exact Or.inl (Or.inr hc)
  · exact Or.inr hc

theorem rlcScaleOneFailure_closed56 (rho : RlcScaleOneConnectorFailure) :
    (rho.1 3 = false ∨ rho.1 4 = false) ∨ rho.1 5 = false := by
  rcases rlcScaleOneFailure_closed_edge rho (mask := 56) (by decide) with ⟨i, hi, hc⟩
  rcases rlcScaleOneMask56_support i hi with rfl | rfl | rfl
  · exact Or.inl (Or.inl hc)
  · exact Or.inl (Or.inr hc)
  · exact Or.inr hc

theorem rlcScaleOneFailure_closed344 (rho : RlcScaleOneConnectorFailure) :
    ((rho.1 3 = false ∨ rho.1 4 = false) ∨ rho.1 6 = false) ∨
      rho.1 8 = false := by
  rcases rlcScaleOneFailure_closed_edge rho (mask := 344) (by decide) with ⟨i, hi, hc⟩
  rcases rlcScaleOneMask344_support i hi with rfl | rfl | rfl | rfl
  · exact Or.inl (Or.inl (Or.inl hc))
  · exact Or.inl (Or.inl (Or.inr hc))
  · exact Or.inl (Or.inr hc)
  · exact Or.inr hc

theorem rlcScaleOneFailure_closed224 (rho : RlcScaleOneConnectorFailure) :
    (rho.1 5 = false ∨ rho.1 6 = false) ∨ rho.1 7 = false := by
  rcases rlcScaleOneFailure_closed_edge rho (mask := 224) (by decide) with ⟨i, hi, hc⟩
  rcases rlcScaleOneMask224_support i hi with rfl | rfl | rfl
  · exact Or.inl (Or.inl hc)
  · exact Or.inl (Or.inr hc)
  · exact Or.inr hc

theorem rlcScaleOneFailure_closed196 (rho : RlcScaleOneConnectorFailure) :
    (rho.1 2 = false ∨ rho.1 6 = false) ∨ rho.1 7 = false := by
  rcases rlcScaleOneFailure_closed_edge rho (mask := 196) (by decide) with ⟨i, hi, hc⟩
  rcases rlcScaleOneMask196_support i hi with rfl | rfl | rfl
  · exact Or.inl (Or.inl hc)
  · exact Or.inl (Or.inr hc)
  · exact Or.inr hc

theorem rlcScaleOneFailure_closed2816 (rho : RlcScaleOneConnectorFailure) :
    (rho.1 8 = false ∨ rho.1 9 = false) ∨ rho.1 11 = false := by
  rcases rlcScaleOneFailure_closed_edge rho (mask := 2816) (by decide) with ⟨i, hi, hc⟩
  rcases rlcScaleOneMask2816_support i hi with rfl | rfl | rfl
  · exact Or.inl (Or.inl hc)
  · exact Or.inl (Or.inr hc)
  · exact Or.inr hc

theorem rlcScaleOneFailure_closed2628 (rho : RlcScaleOneConnectorFailure) :
    ((rho.1 2 = false ∨ rho.1 6 = false) ∨ rho.1 9 = false) ∨
      rho.1 11 = false := by
  rcases rlcScaleOneFailure_closed_edge rho (mask := 2628) (by decide) with ⟨i, hi, hc⟩
  rcases rlcScaleOneMask2628_support i hi with rfl | rfl | rfl | rfl
  · exact Or.inl (Or.inl (Or.inl hc))
  · exact Or.inl (Or.inl (Or.inr hc))
  · exact Or.inl (Or.inr hc)
  · exact Or.inr hc

theorem rlcScaleOneFailure_closed2656 (rho : RlcScaleOneConnectorFailure) :
    ((rho.1 5 = false ∨ rho.1 6 = false) ∨ rho.1 9 = false) ∨
      rho.1 11 = false := by
  rcases rlcScaleOneFailure_closed_edge rho (mask := 2656) (by decide) with ⟨i, hi, hc⟩
  rcases rlcScaleOneMask2656_support i hi with rfl | rfl | rfl | rfl
  · exact Or.inl (Or.inl (Or.inl hc))
  · exact Or.inl (Or.inl (Or.inr hc))
  · exact Or.inl (Or.inr hc)
  · exact Or.inr hc

theorem rlcScaleOneFailure_fiberA
    (rho : RlcScaleOneConnectorFailure)
    (_hclass : rlcScaleOneRouteClass rho.1 = 0) :
    rlcScaleOneSectionAAvoidsSelectedRoutes
      (rlcScaleOneRestrictA rho.1) = true := by
  have h384 := rlcScaleOneFailure_closed384 rho
  have h19 := rlcScaleOneFailure_closed19 rho
  have h7168 := rlcScaleOneFailure_closed7168 rho
  have h28 := rlcScaleOneFailure_closed28 rho
  have h50176 := rlcScaleOneFailure_closed50176 rho
  simp [rlcScaleOneSectionAAvoidsSelectedRoutes,
    rlcScaleOnePairBlockAvoidsRoute, rlcScaleOneFiveBlockAvoidsRoutes,
    rlcScaleOneRestrictA]
  tauto

theorem rlcScaleOneBool_false_of_true_of_false {b : Bool}
    (htrue : b = true) (hfalse : b = false) : False :=
  Bool.false_ne_true (hfalse.symm.trans htrue)

theorem rlcScaleOneFailure_fiberB
    (rho : RlcScaleOneConnectorFailure)
    (hclass : rlcScaleOneRouteClass rho.1 = 1) :
    rlcScaleOneSectionBAvoidsSelectedRoutes
      (rlcScaleOneRestrictB rho.1) = true := by
  have hfix := rlcScaleOneRouteClass_one_fixed rho.1 hclass
  have h19 := rlcScaleOneFailure_closed19 rho
  have h8960 := rlcScaleOneFailure_closed8960 rho
  have h50176 := rlcScaleOneFailure_closed50176 rho
  have h28 := rlcScaleOneFailure_closed28 rho
  have h13312 := rlcScaleOneFailure_closed13312 rho
  have h8800 := rlcScaleOneFailure_closed8800 rho
  have h56 := rlcScaleOneFailure_closed56 rho
  have h8800' : (rho.1 5 = false ∨ rho.1 9 = false) ∨
      rho.1 13 = false := by
    rcases h8800 with h5or6or9 | h13
    · rcases h5or6or9 with h5or6 | h9
      · rcases h5or6 with h5 | h6false
        · exact Or.inl (Or.inl h5)
        · exact (rlcScaleOneBool_false_of_true_of_false hfix.1 h6false).elim
      · exact Or.inl (Or.inr h9)
    · exact Or.inr h13
  simp [rlcScaleOneSectionBAvoidsSelectedRoutes, rlcScaleOneRestrictB]
  exact ⟨⟨⟨⟨⟨⟨h19, h8960⟩, h50176⟩, h28⟩, h13312⟩,
    h8800'⟩, h56⟩

theorem rlcScaleOneFailure_fiberC
    (rho : RlcScaleOneConnectorFailure)
    (hclass : rlcScaleOneRouteClass rho.1 = 2) :
    rlcScaleOneSectionCAvoidsSelectedRoutes
      (rlcScaleOneRestrictC rho.1) = true := by
  have hfix := rlcScaleOneRouteClass_two_fixed rho.1 hclass
  have h7168 := rlcScaleOneFailure_closed7168 rho
  have h19 := rlcScaleOneFailure_closed19 rho
  have h28 := rlcScaleOneFailure_closed28 rho
  have h50176 := rlcScaleOneFailure_closed50176 rho
  have h56 := rlcScaleOneFailure_closed56 rho
  have h344 := rlcScaleOneFailure_closed344 rho
  have h7168' : rho.1 10 = false ∨ rho.1 12 = false := by
    rcases h7168 with h10or11 | h12
    · rcases h10or11 with h10 | h11false
      · exact Or.inl h10
      · exact (rlcScaleOneBool_false_of_true_of_false hfix.2.1 h11false).elim
    · exact Or.inr h12
  have h344' : (rho.1 3 = false ∨ rho.1 4 = false) ∨
      rho.1 8 = false := by
    rcases h344 with h3or4or6 | h8
    · rcases h3or4or6 with h3or4 | h6false
      · exact Or.inl h3or4
      · exact (rlcScaleOneBool_false_of_true_of_false hfix.1 h6false).elim
    · exact Or.inr h8
  simp [rlcScaleOneSectionCAvoidsSelectedRoutes, rlcScaleOneRestrictC]
  exact ⟨⟨⟨⟨⟨h7168', h19⟩, h28⟩, h50176⟩, h56⟩, h344'⟩

theorem rlcScaleOneFailure_fiberD
    (rho : RlcScaleOneConnectorFailure)
    (hclass : rlcScaleOneRouteClass rho.1 = 3) :
    rho.1 2 = false ∧ rho.1 5 = false ∧ rho.1 6 = true ∧
      rho.1 8 = false := by
  have h384 := rlcScaleOneFailure_closed384 rho
  have h224 := rlcScaleOneFailure_closed224 rho
  have h196 := rlcScaleOneFailure_closed196 rho
  have h2816 := rlcScaleOneFailure_closed2816 rho
  have h2628 := rlcScaleOneFailure_closed2628 rho
  have h2656 := rlcScaleOneFailure_closed2656 rho
  have hfix := rlcScaleOneRouteClass_three_fixed rho.1 hclass
  rcases hfix with ⟨h6, h11or7, h9or7⟩
  by_cases h7 : rho.1 7 = false
  · have h11 : rho.1 11 = true := by
      rcases h11or7 with h11 | h7true
      · exact h11
      · exact (rlcScaleOneBool_false_of_true_of_false h7true h7).elim
    have h9 : rho.1 9 = true := by
      rcases h9or7 with h9 | h7true
      · exact h9
      · exact (rlcScaleOneBool_false_of_true_of_false h7true h7).elim
    have h2 : rho.1 2 = false := by
      rcases h2628 with h2or6or9 | h11false
      · rcases h2or6or9 with h2or6 | h9false
        · rcases h2or6 with h2 | h6false
          · exact h2
          · exact (rlcScaleOneBool_false_of_true_of_false h6 h6false).elim
        · exact (rlcScaleOneBool_false_of_true_of_false h9 h9false).elim
      · exact (rlcScaleOneBool_false_of_true_of_false h11 h11false).elim
    have h5 : rho.1 5 = false := by
      rcases h2656 with h5or6or9 | h11false
      · rcases h5or6or9 with h5or6 | h9false
        · rcases h5or6 with h5 | h6false
          · exact h5
          · exact (rlcScaleOneBool_false_of_true_of_false h6 h6false).elim
        · exact (rlcScaleOneBool_false_of_true_of_false h9 h9false).elim
      · exact (rlcScaleOneBool_false_of_true_of_false h11 h11false).elim
    have h8 : rho.1 8 = false := by
      rcases h2816 with h8or9 | h11false
      · rcases h8or9 with h8 | h9false
        · exact h8
        · exact (rlcScaleOneBool_false_of_true_of_false h9 h9false).elim
      · exact (rlcScaleOneBool_false_of_true_of_false h11 h11false).elim
    exact ⟨h2, h5, h6, h8⟩
  · have h7true : rho.1 7 = true := by
      cases h7value : rho.1 7
      · exact (h7 h7value).elim
      · rfl
    have h2 : rho.1 2 = false := by
      rcases h196 with h2or6 | h7false
      · rcases h2or6 with h2 | h6false
        · exact h2
        · exact (rlcScaleOneBool_false_of_true_of_false h6 h6false).elim
      · exact (rlcScaleOneBool_false_of_true_of_false h7true h7false).elim
    have h5 : rho.1 5 = false := by
      rcases h224 with h5or6 | h7false
      · rcases h5or6 with h5 | h6false
        · exact h5
        · exact (rlcScaleOneBool_false_of_true_of_false h6 h6false).elim
      · exact (rlcScaleOneBool_false_of_true_of_false h7true h7false).elim
    have h8 : rho.1 8 = false := by
      rcases h384 with h7false | h8
      · exact (rlcScaleOneBool_false_of_true_of_false h7true h7false).elim
      · exact h8
    exact ⟨h2, h5, h6, h8⟩

end StatMech.Universality
