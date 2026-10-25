/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc73seqcompress.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc60reimerinjection.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerStep.Part3
import Mathlib.Combinatorics.SetFamily.Compression.Down
import Def.StatisticalMechanics.Code.Walls.rc73seqcompress.Part3
set_option linter.style.longLine false

open Finset


namespace StatMech.Walls

open StatMech

variable {α : Type*} [DecidableEq α]


theorem rc73_boxFamily_overcounts :
    2 ^ 2 * (boxFamily reimerStepCexA reimerStepCexB).card
        > (reimerStepCexA.card * reimerStepCexB.card)
    ∧ 2 ^ 2 * (rc73_disjOcc reimerStepCexA reimerStepCexB).card
        ≤ (reimerStepCexA.card * reimerStepCexB.card) := by
  refine ⟨?_, ?_⟩
  · rw [reimerStep_card_box]; decide
  · decide


theorem rc73_disjOcc_downUp_not_monotone_fin3 :
    (rc73_disjOcc (Down.compression 0 ({∅, {0}, {0, 1}, {2}} : Finset (Finset (Fin 3))))
        (rc73_upComp 0 ({∅, {0}, {0, 1}, {0, 2}, {1}, {2}} : Finset (Finset (Fin 3))))).card
      < (rc73_disjOcc ({∅, {0}, {0, 1}, {2}} : Finset (Finset (Fin 3)))
          ({∅, {0}, {0, 1}, {0, 2}, {1}, {2}} : Finset (Finset (Fin 3)))).card := by
  decide


open Classical in


theorem rc73_reimerWprobCore_of_boxUnionBound (h : rc60_BoxUnionBound) : ReimerWprobCore :=
  rc60_reimerWprobCore_of_boxUnionBound h

end StatMech.Walls
