/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.TorusPeriodicLift
import Def.StatisticalMechanics.Code.Onsager.TorusIntersection.Part3


namespace StatMech.Onsager

open BigOperators StatMech.Ising

theorem ons_edgeZBits_divergence_zero
    (L : ℕ) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ evenSubgraphs (onsTorusGraph L))
    (p : ZMod L × ZMod L) :
    ons_horizontalZBit F p +
      ons_horizontalZBit F (p.1 - 1, p.2) +
      ons_verticalZBit F p +
      ons_verticalZBit F (p.1, p.2 - 1) = 0 := by
  exact_mod_cast ons_edgeBits_divergence_zero L F hF p

theorem ons_xFlux_pred
    (L : ℕ) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ evenSubgraphs (onsTorusGraph L))
    (x : ZMod L) :
    ons_xFlux F x = ons_xFlux F (x - 1) := by
  have hsum :
      ∑ y : ZMod L,
        (ons_horizontalZBit F (x, y) +
          ons_horizontalZBit F (x - 1, y) +
          ons_verticalZBit F (x, y) +
          ons_verticalZBit F (x, y - 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro y _
    exact ons_edgeZBits_divergence_zero L F hF (x, y)
  simp only [Finset.sum_add_distrib] at hsum
  have hvshift :
      (∑ y : ZMod L, ons_verticalZBit F (x, y - 1)) =
        ∑ y : ZMod L, ons_verticalZBit F (x, y) := by
    simpa [sub_eq_add_neg] using
      (Equiv.sum_comp (Equiv.addRight (-1 : ZMod L))
        (fun y => ons_verticalZBit F (x, y)))
  rw [hvshift] at hsum
  change ons_xFlux F x = ons_xFlux F (x - 1)
  unfold ons_xFlux
  have hzero :
      (∑ y : ZMod L, ons_horizontalZBit F (x, y)) +
        (∑ y : ZMod L, ons_horizontalZBit F (x - 1, y)) = 0 := by
    let A := ∑ y : ZMod L, ons_horizontalZBit F (x, y)
    let B := ∑ y : ZMod L, ons_horizontalZBit F (x - 1, y)
    let C := ∑ y : ZMod L, ons_verticalZBit F (x, y)
    change A + B + C + C = 0 at hsum
    change A + B = 0
    calc
      A + B = (A + B) + (C + C) := by
        rw [CharTwo.add_self_eq_zero, add_zero]
      _ = A + B + C + C := by abel
      _ = 0 := hsum
  exact (eq_neg_of_add_eq_zero_left hzero).trans
    (CharTwo.neg_eq _)

theorem ons_yFlux_pred
    (L : ℕ) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ evenSubgraphs (onsTorusGraph L))
    (y : ZMod L) :
    ons_yFlux F y = ons_yFlux F (y - 1) := by
  have hsum :
      ∑ x : ZMod L,
        (ons_horizontalZBit F (x, y) +
          ons_horizontalZBit F (x - 1, y) +
          ons_verticalZBit F (x, y) +
          ons_verticalZBit F (x, y - 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    exact ons_edgeZBits_divergence_zero L F hF (x, y)
  simp only [Finset.sum_add_distrib] at hsum
  have hhshift :
      (∑ x : ZMod L, ons_horizontalZBit F (x - 1, y)) =
        ∑ x : ZMod L, ons_horizontalZBit F (x, y) := by
    simpa [sub_eq_add_neg] using
      (Equiv.sum_comp (Equiv.addRight (-1 : ZMod L))
        (fun x => ons_horizontalZBit F (x, y)))
  rw [hhshift] at hsum
  change ons_yFlux F y = ons_yFlux F (y - 1)
  unfold ons_yFlux
  have hzero :
      (∑ x : ZMod L, ons_verticalZBit F (x, y)) +
        (∑ x : ZMod L, ons_verticalZBit F (x, y - 1)) = 0 := by
    let A := ∑ x : ZMod L, ons_horizontalZBit F (x, y)
    let C := ∑ x : ZMod L, ons_verticalZBit F (x, y)
    let D := ∑ x : ZMod L, ons_verticalZBit F (x, y - 1)
    change A + A + C + D = 0 at hsum
    change C + D = 0
    calc
      C + D = (A + A) + (C + D) := by
        rw [CharTwo.add_self_eq_zero, zero_add]
      _ = A + A + C + D := by abel
      _ = 0 := hsum
  exact (eq_neg_of_add_eq_zero_left hzero).trans
    (CharTwo.neg_eq _)

end StatMech.Onsager
