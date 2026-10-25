/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusComplementPotential.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedBoundaryOpenPathPotential
import Def.StatisticalMechanics.Code.FrontierD.IntegralSquareTorusComplementPotential


namespace StatMech.FrontierD

open StatMech.Onsager

open IntegralSquareTorusCycle

noncomputable section

namespace IntegralSquareTorusCycle

variable {L : Nat} [Fact (2 < L)]


@[simp] theorem sub_horizontal (C D : IntegralSquareTorusCycle L)
    (p : ZMod L × ZMod L) :
    (C.sub D).horizontal p = C.horizontal p - D.horizontal p :=
  rfl

@[simp] theorem sub_vertical (C D : IntegralSquareTorusCycle L)
    (p : ZMod L × ZMod L) :
    (C.sub D).vertical p = C.vertical p - D.vertical p :=
  rfl

theorem sub_xFlux (C D : IntegralSquareTorusCycle L) (x : ZMod L) :
    (C.sub D).xFlux x = C.xFlux x - D.xFlux x := by
  unfold xFlux
  simp only [sub_horizontal, Finset.sum_sub_distrib]

theorem sub_yFlux (C D : IntegralSquareTorusCycle L) (y : ZMod L) :
    (C.sub D).yFlux y = C.yFlux y - D.yFlux y := by
  unfold yFlux
  simp only [sub_vertical, Finset.sum_sub_distrib]

theorem zeroFluxHorizontal_eq_horizontal_of_xFlux_eq_zero
    (C : IntegralSquareTorusCycle L) (hC : C.xFlux (-1) = 0)
    (p : ZMod L × ZMod L) :
    C.zeroFluxHorizontal p = C.horizontal p := by
  simp [zeroFluxHorizontal, hC]

theorem zeroFluxVertical_eq_vertical_of_yFlux_eq_zero
    (C : IntegralSquareTorusCycle L) (hC : C.yFlux (-1) = 0)
    (p : ZMod L × ZMod L) :
    C.zeroFluxVertical p = C.vertical p := by
  simp [zeroFluxVertical, hC]


theorem streamPotential_west_sub_of_yFlux_eq_zero
    (C : IntegralSquareTorusCycle L) (hC : C.yFlux (-1) = 0)
    (p : ZMod L × ZMod L) :
    C.streamPotential (p.1 - 1, p.2) - C.streamPotential p =
      C.vertical p := by
  rw [C.streamPotential_vertical_boundary,
    C.zeroFluxVertical_eq_vertical_of_yFlux_eq_zero hC]


theorem streamPotential_north_sub_of_xFlux_eq_zero
    (C : IntegralSquareTorusCycle L) (hC : C.xFlux (-1) = 0)
    (p : ZMod L × ZMod L) :
    C.streamPotential p - C.streamPotential (p.1, p.2 - 1) =
      C.horizontal p := by
  rw [C.streamPotential_horizontal_boundary,
    C.zeroFluxHorizontal_eq_horizontal_of_xFlux_eq_zero hC]

end IntegralSquareTorusCycle
end
end StatMech.FrontierD
