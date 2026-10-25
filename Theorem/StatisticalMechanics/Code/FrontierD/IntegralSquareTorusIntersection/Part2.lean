/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.TorusIntersection.Part8
import Def.StatisticalMechanics.Code.FrontierD.IntegralSquareTorusIntersection.Part2
open scoped BigOperators
open Finset


namespace StatMech.FrontierD

open StatMech.Onsager

noncomputable section

namespace IntegralSquareTorusCycle

variable {L : Nat} [Fact (2 < L)]


theorem zeroFlux_divergence_zero (C : IntegralSquareTorusCycle L)
    (p : ZMod L × ZMod L) :
    C.zeroFluxHorizontal p + C.zeroFluxVertical p -
      C.zeroFluxHorizontal (p.1 - 1, p.2) -
      C.zeroFluxVertical (p.1, p.2 - 1) = 0 := by
  unfold zeroFluxHorizontal zeroFluxVertical
  have h := C.divergence_zero p
  linarith

theorem zeroFluxHorizontal_sum_zero (C : IntegralSquareTorusCycle L)
    (x : ZMod L) :
    ∑ y : ZMod L, C.zeroFluxHorizontal (x, y) = 0 := by
  unfold zeroFluxHorizontal
  rw [Finset.sum_sub_distrib]
  change C.xFlux x -
    (∑ y : ZMod L, if y = 0 then C.xFlux (-1) else 0) = 0
  rw [C.xFlux_eq_neg_one x]
  simp

theorem zeroFluxVertical_sum_zero (C : IntegralSquareTorusCycle L)
    (y : ZMod L) :
    ∑ x : ZMod L, C.zeroFluxVertical (x, y) = 0 := by
  unfold zeroFluxVertical
  rw [Finset.sum_sub_distrib]
  change C.yFlux y -
    (∑ x : ZMod L, if x = 0 then C.yFlux (-1) else 0) = 0
  rw [C.yFlux_eq_neg_one y]
  simp

theorem zmodPrefix_sub_pred_of_sum_zero
    (f : ZMod L → Int) (hsum : ∑ z, f z = 0) (z : ZMod L) :
    ons_zmodPrefix f z - ons_zmodPrefix f (z - 1) = f z := by
  by_cases hz : z = 0
  · subst z
    have hrange := ons_sum_zmod_eq_sum_range L f
    have hgt : 2 < L := Fact.out
    have hL : L = (L - 1) + 1 := by omega
    have hdecomp :
        (∑ i ∈ Finset.range L, f (i : ZMod L)) =
          f 0 + ∑ i ∈ Finset.range (L - 1),
            f ((i + 1 : Nat) : ZMod L) := by
      rw [show Finset.range L = Finset.range ((L - 1) + 1) by
        exact congrArg Finset.range hL]
      simpa only [Nat.cast_zero] using
        ons_sum_range_succ_first (fun i : Nat => f (i : ZMod L)) (L - 1)
    rw [hdecomp, hsum] at hrange
    have hprefix :
        (∑ i ∈ Finset.range (L - 1),
          f ((i + 1 : Nat) : ZMod L)) = ons_zmodPrefix f (-1) := by
      unfold ons_zmodPrefix
      rw [ons_zmod_val_neg_one]
    have hpref : ons_zmodPrefix f (-1) = -f 0 := by
      rw [← hprefix]
      linarith
    rw [zero_sub, ons_zmodPrefix_zero, hpref]
    ring
  · rw [ons_zmodPrefix_eq_add_pred f z hz]
    abel


end IntegralSquareTorusCycle
end
end StatMech.FrontierD
