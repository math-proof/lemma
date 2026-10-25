/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc25doubledcover.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc24countbridge.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyStep
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


set_option maxRecDepth 100000 in

set_option maxHeartbeats 40000000 in


theorem rc25_boxDownUp_strictDecrease :
    #(rc20_famCylBox
        (Down.compression 0 ({∅, {0}, {1}, {2}, {0,1}, {0,2}} : Finset (Finset (Fin 3))))
        (rc22_upComp 0 ({∅, {0}, {2}, {0,1}} : Finset (Finset (Fin 3)))))
      < #(rc20_famCylBox ({∅, {0}, {1}, {2}, {0,1}, {0,2}} : Finset (Finset (Fin 3)))
        ({∅, {0}, {2}, {0,1}})) := by
  rw [← rc24_upCompComp_eq, ← rc20_famCylBoxComp_eq, ← rc20_famCylBoxComp_eq]
  decide


theorem rc25_boxDownUpMono_false : ¬ rc24_BoxDownUpMono := by
  intro h
  have hle := h 3 ({∅, {0}, {1}, {2}, {0,1}, {0,2}})
    ({∅, {0}, {2}, {0,1}}) 0
  exact absurd hle (not_le.mpr rc25_boxDownUp_strictDecrease)


end StatMech.Walls
