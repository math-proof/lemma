/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisSubdivision.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardIntegralAxisWord.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardForwardSubdivision
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardChordPhaseGlue.Part2
import Theorem.StatisticalMechanics.Code.Onsager.PeriodicTurnClosure.Part9
import Def.StatisticalMechanics.Code.FrontierA.KacWardIntegralAxisSubdivision.Part2


namespace StatMech.FrontierA

open Set

open scoped BigOperators

open StatMech.Onsager.BaseCase


@[simp] theorem kwPrefixPositions_nil : kwPrefixPositions [] = [] := rfl

@[simp] theorem kwPrefixPositions_cons (d : Fin 4) (tail : List (Fin 4)) :
    kwPrefixPositions (d :: tail) =
      0 :: (kwPrefixPositions tail).map (stepOf d + ·) := rfl

@[simp] theorem kwPrefixPositions_length (word : List (Fin 4)) :
    (kwPrefixPositions word).length = word.length := by
  induction word with
  | nil => rfl
  | cons d tail ih => simp [ih]

theorem kwPrefixPositions_append (left right : List (Fin 4)) :
    kwPrefixPositions (left ++ right) =
      kwPrefixPositions left ++
        (kwPrefixPositions right).map
          (((left.map stepOf).sum) + ·) := by
  induction left with
  | nil => simp
  | cons d tail ih =>
      simp only [List.cons_append, kwPrefixPositions_cons, List.map_cons,
        List.sum_cons, ih, List.map_append, List.cons_append]
      simp only [List.map_map, Function.comp_def, add_assoc]

theorem kwPrefixPositions_get
    (word : List (Fin 4)) (k : Fin word.length) :
    (kwPrefixPositions word).get
        ⟨k.val, by simpa using k.isLt⟩ =
      ((word.take k.val).map stepOf).sum := by
  induction word with
  | nil => exact Fin.elim0 k
  | cons d tail ih =>
      refine Fin.cases ?_ (fun q ↦ ?_) k
      · simp
      · simp only [Fin.val_succ, List.take_succ_cons, List.map_cons,
          List.sum_cons, kwPrefixPositions_cons, List.get_eq_getElem,
          List.getElem_cons_succ, List.getElem_map]
        have hq := ih q
        simp only [List.get_eq_getElem] at hq
        rw [hq]


end StatMech.FrontierA
