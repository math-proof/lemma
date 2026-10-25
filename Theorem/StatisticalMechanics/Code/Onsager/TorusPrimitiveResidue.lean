/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveResidue.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.IntegralSquareTorusResiduePotential
import Theorem.StatisticalMechanics.Code.Onsager.TorusPrimitiveParity
import Def.StatisticalMechanics.Code.Onsager.TorusPrimitiveResidue
open scoped BigOperators


namespace StatMech.Onsager

open StatMech.FrontierD

open StatMech.FrontierD.IntegralSquareTorusCycle

noncomputable section

theorem ons_portEdge_eq_positiveHorizontal_of_horizontal
    {L : Nat} (d : ons_Dart L) (hdir : d.2 = 0 ∨ d.2 = 2) :
    ons_portEdge L d = ons_portEdge L (ons_positiveHorizontalSource d, 0) := by
  rcases d with ⟨z, mu⟩
  rcases hdir with hdir | hdir
  · change mu = 0 at hdir
    rw [hdir]
    rfl
  · change mu = 2 at hdir
    rw [hdir]
    exact ons_portEdge_west_eq_horizontal L z

theorem ons_portEdge_eq_positiveVertical_of_vertical
    {L : Nat} (d : ons_Dart L) (hdir : d.2 = 1 ∨ d.2 = 3) :
    ons_portEdge L d = ons_portEdge L (ons_positiveVerticalSource d, 1) := by
  rcases d with ⟨z, mu⟩
  rcases hdir with hdir | hdir
  · change mu = 1 at hdir
    rw [hdir]
    rfl
  · change mu = 3 at hdir
    rw [hdir]
    exact ons_portEdge_south_eq_vertical L z

theorem ons_portEdge_eq_of_dartHorizontal_ne_zero
    {L : Nat} (d : ons_Dart L) (z : ZMod L × ZMod L)
    (h : IntegralSquareTorusCycle.dartHorizontal d z ≠ 0) :
    ons_portEdge L d = ons_portEdge L (z, 0) := by
  rcases d with ⟨⟨x, y⟩, mu⟩
  fin_cases mu
  · change IntegralSquareTorusCycle.pointMass (x, y) z ≠ 0 at h
    by_cases hz : z = (x, y)
    · subst z
      rfl
    · simp [IntegralSquareTorusCycle.pointMass, hz] at h
  · simp [IntegralSquareTorusCycle.dartHorizontal] at h
  · change -IntegralSquareTorusCycle.pointMass (x - 1, y) z ≠ 0 at h
    by_cases hz : z = (x - 1, y)
    · subst z
      exact ons_portEdge_west_eq_horizontal L (x, y)
    · simp [IntegralSquareTorusCycle.pointMass, hz] at h
  · simp [IntegralSquareTorusCycle.dartHorizontal] at h

theorem ons_portEdge_eq_of_dartVertical_ne_zero
    {L : Nat} (d : ons_Dart L) (z : ZMod L × ZMod L)
    (h : IntegralSquareTorusCycle.dartVertical d z ≠ 0) :
    ons_portEdge L d = ons_portEdge L (z, 1) := by
  rcases d with ⟨⟨x, y⟩, mu⟩
  fin_cases mu
  · simp [IntegralSquareTorusCycle.dartVertical] at h
  · change IntegralSquareTorusCycle.pointMass (x, y) z ≠ 0 at h
    by_cases hz : z = (x, y)
    · subst z
      rfl
    · simp [IntegralSquareTorusCycle.pointMass, hz] at h
  · simp [IntegralSquareTorusCycle.dartVertical] at h
  · change -IntegralSquareTorusCycle.pointMass (x, y - 1) z ≠ 0 at h
    by_cases hz : z = (x, y - 1)
    · subst z
      exact ons_portEdge_south_eq_vertical L (x, y)
    · simp [IntegralSquareTorusCycle.pointMass, hz] at h

theorem IntegralSquareTorusCycle.ofDarts_horizontal_eq_zero_of_not_mem
    {L n : Nat} [Fact (2 < L)] [NeZero n]
    (v : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
    (z : ZMod L × ZMod L)
    (hnot : ons_portEdge L (z, 0) ∉ ons_dartEdgeSet v) :
    (IntegralSquareTorusCycle.ofDarts v hvalid).horizontal z = 0 := by
  change (∑ k, IntegralSquareTorusCycle.dartHorizontal (v k) z) = 0
  apply Finset.sum_eq_zero
  intro k _
  by_contra hk
  apply hnot
  rw [ons_dartEdgeSet, Finset.mem_image]
  exact ⟨k, Finset.mem_univ _,
    ons_portEdge_eq_of_dartHorizontal_ne_zero (v k) z hk⟩

theorem IntegralSquareTorusCycle.ofDarts_vertical_eq_zero_of_not_mem
    {L n : Nat} [Fact (2 < L)] [NeZero n]
    (v : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
    (z : ZMod L × ZMod L)
    (hnot : ons_portEdge L (z, 1) ∉ ons_dartEdgeSet v) :
    (IntegralSquareTorusCycle.ofDarts v hvalid).vertical z = 0 := by
  change (∑ k, IntegralSquareTorusCycle.dartVertical (v k) z) = 0
  apply Finset.sum_eq_zero
  intro k _
  by_contra hk
  apply hnot
  rw [ons_dartEdgeSet, Finset.mem_image]
  exact ⟨k, Finset.mem_univ _,
    ons_portEdge_eq_of_dartVertical_ne_zero (v k) z hk⟩


end
end StatMech.Onsager
