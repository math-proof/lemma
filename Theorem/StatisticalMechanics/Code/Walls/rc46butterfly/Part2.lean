/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc46butterfly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc45doubledcover.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
import Def.StatisticalMechanics.Code.Walls.rc46butterfly.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem rc46_downDownStep_decreases_famCylBox_fin3 :
    (rc20_famCylBoxComp 3 (Down.compression 1 rc46_Adn) (Down.compression 1 rc46_Bdn)).card
      < (rc20_famCylBoxComp 3 rc46_Adn rc46_Bdn).card := by
  rw [rc46_Adn, rc46_Bdn]; decide


theorem rc46_downDownStep_reflInter_stable_fin3 :
    (rc20_reflInterComp 3 (Down.compression 1 rc46_Adn) (Down.compression 1 rc46_Bdn)).card
      = (rc20_reflInterComp 3 rc46_Adn rc46_Bdn).card := by
  rw [rc46_Adn, rc46_Bdn]; decide


end StatMech.Walls
