/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc6deficitform.Part4
import Theorem.StatisticalMechanics.Code.Walls.rc6relabelinvariance.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc6eventdowncompression
import Theorem.StatisticalMechanics.Code.Walls.rc6blmonovariant
import Theorem.StatisticalMechanics.Code.Walls.rc6hallavailable.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc6canonicalwitness.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc6overlapsplit
import Theorem.StatisticalMechanics.Code.Walls.rc6localmirror.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc5_core.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.Reimer2000Close.Part5
import Def.StatisticalMechanics.Code.Walls.rc6core.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace


section MirrorInjectivity

variable {α : Type*} [Fintype α] [DecidableEq α]

open Classical in
omit [Fintype α] [DecidableEq α] in


theorem rc6_boxReflectInjection_of_mirrorInjectivity (A B : Set (ConfigSpace α))
    (h : rc6_MirrorInjectivity A B) : rc5_BoxReflectInjection A B := by
  obtain ⟨S, hmem, hinj⟩ := h
  exact ⟨fun ω => rc6_mirrorL {a | S ω a = true} ω, hinj, hmem⟩

end MirrorInjectivity


theorem rc6_witnessTied_injectivity_false : ¬ poc_WitnessInjection rbi_A rbi_B :=
  poc_witnessInjection_rbi_false


end StatMech.Walls
