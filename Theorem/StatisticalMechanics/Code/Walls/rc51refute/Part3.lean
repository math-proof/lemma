/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc51refute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc50hall.Part3
import Def.StatisticalMechanics.Code.Walls.rc51refute.Part3
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace


set_option maxHeartbeats 8000000 in
set_option maxRecDepth 10000 in


theorem rc51_hallCond_refuter_false :
    rc51_hallCondComp 3 rc51_Aref rc51_Bref = false := by
  rw [rc51_hallCondComp, rc51_Aref, rc51_Bref]; decide

open Classical in


theorem rc51_not_hallCond_refuter : ¬ rc49_HallCond rc51_Aref rc51_Bref :=
  rc51_not_hallCond_of_comp_false 3 rc51_Aref rc51_Bref rc51_hallCond_refuter_false

open Classical in


theorem rc51_not_injectiveSelection_refuter : ¬ rc50_InjectiveSelection rc51_Aref rc51_Bref := by
  intro h
  exact rc51_not_hallCond_refuter ((rc50_hall_iff_injectiveSelection rc51_Aref rc51_Bref).mpr h)

open Classical in


theorem rc51_not_hallDoubled : ¬ rc49_HallDoubled := by
  intro h
  exact rc51_not_hallCond_refuter (h 3 rc51_Aref rc51_Bref)

open Classical in


theorem rc51_not_injectiveSelectionAll : ¬ rc50_InjectiveSelectionAll := by
  intro h
  exact rc51_not_injectiveSelection_refuter (h 3 rc51_Aref rc51_Bref)


set_option maxRecDepth 4000 in


theorem rc51_box_refuter_eq :
    rc20_famCylBox rc51_Aref rc51_Bref = {({0} : Finset (Fin 3)), ({1} : Finset (Fin 3))} := by
  rw [← rc20_famCylBoxComp_eq, rc51_Aref, rc51_Bref]; decide

set_option maxRecDepth 4000 in


theorem rc51_reflInter_refuter_eq :
    rc10_reflInter rc51_Aref rc51_Bref
      = {(∅ : Finset (Fin 3)), ({0} : Finset (Fin 3)), ({1} : Finset (Fin 3))} := by
  rw [← rc20_reflInterComp_eq, rc51_Aref, rc51_Bref]; decide

set_option maxRecDepth 4000 in


theorem rc51_wall_refuter_holds :
    (rc20_famCylBoxComp 3 rc51_Aref rc51_Bref).card
      ≤ (rc20_reflInterComp 3 rc51_Aref rc51_Bref).card := by
  rw [rc51_Aref, rc51_Bref]; decide


open Classical in


theorem rc51_reimer_route_refuted :
    (rc51_hallCondComp 3 rc51_Aref rc51_Bref = false)
      ∧ ¬ rc49_HallCond rc51_Aref rc51_Bref
      ∧ ¬ rc50_InjectiveSelection rc51_Aref rc51_Bref
      ∧ ¬ rc49_HallDoubled
      ∧ ¬ rc50_InjectiveSelectionAll
      ∧ (rc20_famCylBox rc51_Aref rc51_Bref = {({0} : Finset (Fin 3)), ({1} : Finset (Fin 3))})
      ∧ ((rc20_famCylBoxComp 3 rc51_Aref rc51_Bref).card
          ≤ (rc20_reflInterComp 3 rc51_Aref rc51_Bref).card) :=
  ⟨rc51_hallCond_refuter_false,
    rc51_not_hallCond_refuter,
    rc51_not_injectiveSelection_refuter,
    rc51_not_hallDoubled,
    rc51_not_injectiveSelectionAll,
    rc51_box_refuter_eq,
    rc51_wall_refuter_holds⟩

end StatMech.Walls
