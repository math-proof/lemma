/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.TorusIntersection.Part8
import Def.StatisticalMechanics.Code.FrontierD.IntegralSquareTorusIntersection
open scoped BigOperators
open Finset


namespace StatMech.FrontierD

open StatMech.Onsager

noncomputable section

namespace IntegralSquareTorusCycle

variable {L : Nat} [Fact (2 < L)]


theorem xFlux_pred (C : IntegralSquareTorusCycle L) (x : ZMod L) :
    C.xFlux x = C.xFlux (x - 1) := by
  have hsum :
      ∑ y : ZMod L,
        (C.horizontal (x, y) + C.vertical (x, y) -
          C.horizontal (x - 1, y) - C.vertical (x, y - 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro y _
    exact C.divergence_zero (x, y)
  have hvshift :
      (∑ y : ZMod L, C.vertical (x, y - 1)) =
        ∑ y : ZMod L, C.vertical (x, y) := by
    simpa [sub_eq_add_neg] using
      (Equiv.sum_comp (Equiv.addRight (-1 : ZMod L))
        (fun y => C.vertical (x, y)))
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsum
  rw [hvshift] at hsum
  unfold xFlux
  linarith

theorem yFlux_pred (C : IntegralSquareTorusCycle L) (y : ZMod L) :
    C.yFlux y = C.yFlux (y - 1) := by
  have hsum :
      ∑ x : ZMod L,
        (C.horizontal (x, y) + C.vertical (x, y) -
          C.horizontal (x - 1, y) - C.vertical (x, y - 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    exact C.divergence_zero (x, y)
  have hhshift :
      (∑ x : ZMod L, C.horizontal (x - 1, y)) =
        ∑ x : ZMod L, C.horizontal (x, y) := by
    simpa [sub_eq_add_neg] using
      (Equiv.sum_comp (Equiv.addRight (-1 : ZMod L))
        (fun x => C.horizontal (x, y)))
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsum
  rw [hhshift] at hsum
  unfold yFlux
  linarith

theorem xFlux_eq_neg_one (C : IntegralSquareTorusCycle L) (x : ZMod L) :
    C.xFlux x = C.xFlux (-1) :=
  ons_zmod_eq_neg_one_of_eq_pred C.xFlux C.xFlux_pred x

theorem yFlux_eq_neg_one (C : IntegralSquareTorusCycle L) (y : ZMod L) :
    C.yFlux y = C.yFlux (-1) :=
  ons_zmod_eq_neg_one_of_eq_pred C.yFlux C.yFlux_pred y


end IntegralSquareTorusCycle
end
end StatMech.FrontierD
