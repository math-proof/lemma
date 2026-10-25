/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WindingParity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.ShermanPropIV.Part2
import Def.StatisticalMechanics.Code.Onsager.WindingParity


namespace StatMech.Onsager

open BigOperators


theorem wpar_straight_step :
    ∀ k : Fin 2, wpar_siteStraight k.succ
      = ons_dirStep 2 (wpar_dStraight k.castSucc) (wpar_siteStraight k.castSucc) := by
  decide


theorem wpar_straight_nu :
    ∀ k : Fin 2, wpar_dStraight k.succ ≠ wpar_dStraight k.castSucc + 2 := by
  decide


theorem wpar_straight_closeDir : wpar_dStraight (Fin.last 2) = wpar_dStraight 0 := by
  decide


theorem wpar_straight_closeSite : wpar_siteStraight (Fin.last 2) = wpar_siteStraight 0 := by
  decide


theorem wpar_straight_selfAvoiding : ons_SelfAvoiding wpar_siteStraight := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> revert hab <;> decide


theorem wpar_straight_turnSum :
    (∑ k : Fin 2, ons_turnPow (wpar_dStraight k.castSucc) (wpar_dStraight k.succ)) = 4 * 0 := by
  decide


theorem wpar_umlaufsatzKW_false : ¬ ons_DiscreteUmlaufsatzKW := by
  intro hU
  have hodd : Odd (0 : ℤ) :=
    hU 2 2 wpar_dStraight wpar_siteStraight
      wpar_straight_step wpar_straight_nu wpar_straight_closeDir wpar_straight_closeSite
      wpar_straight_selfAvoiding 0 wpar_straight_turnSum
  rcases hodd with ⟨k, hk⟩
  omega


end StatMech.Onsager
