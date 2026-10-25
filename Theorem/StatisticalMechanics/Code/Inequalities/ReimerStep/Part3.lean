/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerStep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompression.Part5
import Mathlib.Data.Finset.Prod
import Def.StatisticalMechanics.Code.Inequalities.ReimerStep.Part3
open Finset
open scoped FinsetFamily


namespace StatMech

variable {α : Type*} [DecidableEq α]


lemma reimerStep_card_box : (boxFamily reimerStepCexA reimerStepCexB).card = 3 := by
  decide


lemma reimerStep_card_box_compressed :
    (boxFamily (Down.compression 0 reimerStepCexA)
      (Down.compression 0 reimerStepCexB)).card = 2 := by
  decide


theorem reimerStep_box_compression_false :
    ∃ (𝒜 ℬ : Finset (Finset (Fin 2))) (i : Fin 2),
      (boxFamily (Down.compression i 𝒜) (Down.compression i ℬ)).card
        < (boxFamily 𝒜 ℬ).card :=
  ⟨reimerStepCexA, reimerStepCexB, 0, by
    rw [reimerStep_card_box, reimerStep_card_box_compressed]; norm_num⟩


end StatMech
