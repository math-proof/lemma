/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc55nonproduct.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc54weighted.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc46butterfly.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc38butterflymono
import Theorem.StatisticalMechanics.Code.Walls.rc22doublecover.Part6
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem rc55_famCylBox_downDown_strictly_decreases_fin3 :
    #(rc20_famCylBox (Down.compression 1 rc46_Adn) (Down.compression 1 rc46_Bdn))
      < #(rc20_famCylBox rc46_Adn rc46_Bdn) := by
  rw [← rc20_famCylBoxComp_eq, ← rc20_famCylBoxComp_eq]
  exact rc46_downDownStep_decreases_famCylBox_fin3


theorem rc55_boxCompressionMono_false : ¬ rc22_BoxCompressionMono := by
  intro h
  have := h 3 rc46_Adn rc46_Bdn 1
  exact absurd this (not_le.mpr rc55_famCylBox_downDown_strictly_decreases_fin3)


end StatMech.Walls
