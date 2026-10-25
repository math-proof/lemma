/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyProve3.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyClose.Part5
import Theorem.StatisticalMechanics.Code.Walls.rc_dpairsfiberrecursion
import Theorem.StatisticalMechanics.Code.Walls.rc_dpairsmodular
import Theorem.StatisticalMechanics.Code.Walls.rmr_reflectinvolution.Part2
import Theorem.StatisticalMechanics.Code.Walls.rmr_baseanddisjoint
import Def.StatisticalMechanics.Code.Walls.rc_core
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech

variable {α : Type*} [DecidableEq α]


theorem rc_core_countBoxBridge_iff : rc_core_CountBoxBridge ↔ StatMech.poc_SlabCardAll := Iff.rfl


theorem rc_core_reimer_of_bridge (h : rc_core_CountBoxBridge) : ReimerWprobCore :=
  reimer_wprob_core_of_slabCard h

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in


theorem rc_core_reimer_inequality_of_bridge (h : rc_core_CountBoxBridge) {E : Type*}
    [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1) (A B : Set (ConfigSpace E)) :
    (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B)
      ≤ (bernoulliProductMeasure (E := E) p hp).real A
        * (bernoulliProductMeasure (E := E) p hp).real B :=
  reimer_inequality_of_slabCard h hp A B


variable {β : Type*} [Fintype β] [DecidableEq β]


theorem rc_core_bridge_of_disjoint_support {A B : Set (ConfigSpace β)} {S T : Finset β}
    (hA : StatMech.DependsOn A (↑S)) (hB : StatMech.DependsOn B (↑T)) (hST : Disjoint S T) :
    poc_SlabCard A B :=
  rmr_slabCard_of_disjoint_support hA hB hST


theorem rc_core_bridge_one (A B : Set (ConfigSpace (Fin 1))) : poc_SlabCard A B :=
  rmr_slabCard_one A B


theorem rc_core_bridge_of_box_empty {A B : Set (ConfigSpace β)}
    (hbox : disjointOccurrence A B = ∅) : poc_SlabCard A B :=
  poc_slabCard_of_box_empty hbox

end StatMech.Walls
