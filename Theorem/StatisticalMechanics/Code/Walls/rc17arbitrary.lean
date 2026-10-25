/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc17arbitrary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc16sliceunion
import Theorem.StatisticalMechanics.Code.Walls.rc9core.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc8core.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.Reimer.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyInjClose.Part2
open Finset MeasureTheory
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc17_deficit_incInc {n : ℕ} {A B : Set (ConfigSpace (Fin n))}
    (hA : IsIncreasing A) (hB : IsIncreasing B) : rc5_deficit A B ≤ 0 :=
  rc16_deficitBridgeIncInc n A B hA hB

open Classical in


theorem rc17_deficit_decDec {n : ℕ} {A B : Set (ConfigSpace (Fin n))}
    (hA : IsDecreasing A) (hB : IsDecreasing B) : rc5_deficit A B ≤ 0 :=
  rc9_decDec_of_incInc (fun {C D} hC hD => rc16_deficitBridgeIncInc n C D hC hD) hA hB

open Classical in


theorem rc17_deficit_le_zero_of_bothMonotone {n : ℕ} {A B : Set (ConfigSpace (Fin n))}
    (hA : IsIncreasing A ∨ IsDecreasing A) (hB : IsIncreasing B ∨ IsDecreasing B) :
    rc5_deficit A B ≤ 0 := by
  rcases hA with hAi | hAd
  · rcases hB with hBi | hBd
    · exact rc17_deficit_incInc hAi hBi
    · exact rc8_deficit_le_zero_inc_dec hAi hBd
  · rcases hB with hBi | hBd
    · exact rc8_deficit_le_zero_dec_inc hAd hBi
    · exact rc17_deficit_decDec hAd hBd


end StatMech.Walls
