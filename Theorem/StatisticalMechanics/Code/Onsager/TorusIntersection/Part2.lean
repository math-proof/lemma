/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.TorusPeriodicLift
import Def.StatisticalMechanics.Code.Onsager.TorusIntersection.Part2


namespace StatMech.Onsager

open BigOperators StatMech.Ising

theorem ons_edgeBit_eq_zero_of_incCount_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : Finset (Sym2 V)) (v : V) (e : Sym2 V)
    (hinc : incCount F v = 0) (hve : v ∈ e) :
    ons_edgeBit F e = 0 := by
  by_cases heF : e ∈ F
  · have hpos : 0 < incCount F v := by
      unfold incCount
      apply Finset.card_pos.mpr
      exact ⟨e, Finset.mem_filter.mpr ⟨heF, hve⟩⟩
    rw [hinc] at hpos
    omega
  · simp [ons_edgeBit, heF]

theorem ons_horizontalBit_zero_of_incCount_eq_zero
    {L : ℕ} [NeZero L]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (p : ZMod L × ZMod L) (hinc : incCount F p = 0) :
    ons_horizontalBit F p = 0 := by
  apply ons_edgeBit_eq_zero_of_incCount_eq_zero F p
    (ons_portEdge L (p, 0)) hinc
  simp [ons_portEdge]

theorem ons_verticalBit_zero_of_incCount_eq_zero
    {L : ℕ} [NeZero L]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (p : ZMod L × ZMod L) (hinc : incCount F p = 0) :
    ons_verticalBit F p = 0 := by
  apply ons_edgeBit_eq_zero_of_incCount_eq_zero F p
    (ons_portEdge L (p, 1)) hinc
  simp [ons_portEdge]

theorem ons_verticalBit_pred_zero_of_incCount_eq_zero
    {L : ℕ} [NeZero L]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (p : ZMod L × ZMod L) (hinc : incCount F p = 0) :
    ons_verticalBit F (p.1, p.2 - 1) = 0 := by
  apply ons_edgeBit_eq_zero_of_incCount_eq_zero F p
    (ons_portEdge L ((p.1, p.2 - 1), 1)) hinc
  rcases p with ⟨x, y⟩
  simp [ons_portEdge, ons_dirStep]

theorem ons_horizontalBit_pred_zero_of_incCount_eq_zero
    {L : ℕ} [NeZero L]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (p : ZMod L × ZMod L) (hinc : incCount F p = 0) :
    ons_horizontalBit F (p.1 - 1, p.2) = 0 := by
  apply ons_edgeBit_eq_zero_of_incCount_eq_zero F p
    (ons_portEdge L ((p.1 - 1, p.2), 0)) hinc
  rcases p with ⟨x, y⟩
  simp [ons_portEdge, ons_dirStep]

theorem ons_edgeCycleIntersection_eq_zero_of_incCount_disjoint
    {L : ℕ} [NeZero L]
    (F G : Finset (Sym2 (ZMod L × ZMod L)))
    (hdisj : ∀ p, incCount F p = 0 ∨ incCount G p = 0) :
    ons_edgeCycleIntersection F G = 0 := by
  unfold ons_edgeCycleIntersection
  apply Finset.sum_eq_zero
  intro p _
  rcases hdisj p with hF | hG
  · rw [ons_horizontalBit_zero_of_incCount_eq_zero F p hF,
      ons_verticalBit_zero_of_incCount_eq_zero F p hF]
    simp
  · rw [ons_verticalBit_pred_zero_of_incCount_eq_zero G p hG,
      ons_horizontalBit_pred_zero_of_incCount_eq_zero G p hG]
    simp

end StatMech.Onsager
