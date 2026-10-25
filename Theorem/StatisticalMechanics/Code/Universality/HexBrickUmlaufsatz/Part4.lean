/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBrickUmlaufsatz.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.GeneralUmlaufsatz
import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part18
import Def.StatisticalMechanics.Code.Universality.HexBrickUmlaufsatz.Part4


namespace StatMech.Universality

open Finset

open StatMech.Onsager.BaseCase

open StatMech.Onsager


theorem hex_turnSum_eq_neg_six_of_interiorOnLeft {n : ℕ} [NeZero n]
    (heading : Fin n → Fin 6) (turn : Fin n → ℤ)
    (hlegal : ∀ i, turn i = 1 ∨ turn i = -1)
    (hstep : ∀ i, heading (i + 1) = hexHeadingTurn (heading i) (turn i))
    (hclosed : ∑ i, stepOf (hexBrickDir (heading i)) = 0)
    (hsimple : Function.Injective
      (pos (fun i => hexBrickDir (heading i))))
    (hn : 3 ≤ n) (horient : HexBrickInteriorOnLeft heading) :
    (∑ i, turn i) = -6 := by
  let d : Fin n → Fin 4 := fun i => hexBrickDir (heading i)
  have hnu : ∀ i, d (i + 1) ≠ d i + 2 := by
    intro i
    rw [show d (i + 1) = hexBrickDir (heading (i + 1)) by rfl,
      hstep i]
    exact hexBrickDir_turn_ne_opposite (heading i) (turn i) (hlegal i)
  have hwalk :=
    StatMech.Onsager.GeneralUmlaufsatz.cornerDiff_eq_sign_mul_turnSum
      d hclosed hsimple hn hnu
  have hpinch :=
    StatMech.Onsager.PinchFree.pinchCount_eq_zero d hclosed hsimple hn
  have hchi : StatMech.Onsager.CellEuler.eulerChar
      (StatMech.Onsager.InteriorCells.interiorCells d hclosed) = 1 := by
    obtain ⟨m, hm⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    subst n
    exact
      StatMech.Onsager.GeneralInterior.eulerChar_interiorCells_eq_one
        d hclosed hsimple
  have hgb :=
    StatMech.Onsager.CellGaussBonnetGlobal.cornerDiff_eq
      (StatMech.Onsager.InteriorCells.interiorCells d hclosed)
  rw [hchi, hpinch] at hgb
  norm_num at hgb
  change StatMech.Onsager.Orientation.leftParity d 0 = 1 at horient
  rw [if_pos horient, one_mul] at hwalk
  have hrect :
      (∑ i, ons_turnPow (d i) (d (i + 1))) = 4 :=
    hwalk.symm.trans hgb
  have htel := hexBrick_turn_telescope heading turn hlegal hstep
  change 2 * (∑ i, turn i) +
      3 * (∑ i, ons_turnPow (d i) (d (i + 1))) = 0 at htel
  omega


theorem hex_turnSum_eq_six_or_neg_six {n : ℕ} [NeZero n]
    (heading : Fin n → Fin 6) (turn : Fin n → ℤ)
    (hlegal : ∀ i, turn i = 1 ∨ turn i = -1)
    (hstep : ∀ i, heading (i + 1) = hexHeadingTurn (heading i) (turn i))
    (hclosed : ∑ i, stepOf (hexBrickDir (heading i)) = 0)
    (hsimple : Function.Injective
      (pos (fun i => hexBrickDir (heading i))))
    (hn : 3 ≤ n) :
    (∑ i, turn i) = 6 ∨ (∑ i, turn i) = -6 := by
  let d : Fin n → Fin 4 := fun i => hexBrickDir (heading i)
  have hnu : ∀ i, d (i + 1) ≠ d i + 2 := by
    intro i
    rw [show d (i + 1) = hexBrickDir (heading (i + 1)) by rfl,
      hstep i]
    exact hexBrickDir_turn_ne_opposite (heading i) (turn i) (hlegal i)
  have hrect :=
    StatMech.Onsager.GeneralUmlaufsatz.turnSum_eq_four_or_neg_four
      d hclosed hsimple hn hnu
  have htel := hexBrick_turn_telescope heading turn hlegal hstep
  change 2 * (∑ i, turn i) +
      3 * (∑ i, ons_turnPow (d i) (d (i + 1))) = 0 at htel
  rcases hrect with hfour | hnegfour
  · right
    change (∑ i, turn i) = -6
    change (∑ i, ons_turnPow (d i) (d (i + 1))) = 4 at hfour
    omega
  · left
    change (∑ i, turn i) = 6
    change (∑ i, ons_turnPow (d i) (d (i + 1))) = -4 at hnegfour
    omega


theorem HexAWBrickCycle.turnSum_eq_six_or_neg_six {n : ℕ} [NeZero n]
    (C : HexAWBrickCycle n) (turn : Fin n → ℤ)
    (hlegal : ∀ i, turn i = 1 ∨ turn i = -1)
    (hstep : ∀ i, C.heading (i + 1) =
      hexHeadingTurn (C.heading i) (turn i))
    (hn : 3 ≤ n) :
    (∑ i, turn i) = 6 ∨ (∑ i, turn i) = -6 := by
  apply hex_turnSum_eq_six_or_neg_six C.heading turn hlegal hstep
  · simpa [HexAWBrickCycle.direction] using C.closed
  · simpa [HexAWBrickCycle.direction] using C.pos_injective
  · exact hn


theorem HexAWBrickCycle.turnSum_eq_neg_six {n : ℕ} [NeZero n]
    (C : HexAWBrickCycle n) (turn : Fin n → ℤ)
    (hlegal : ∀ i, turn i = 1 ∨ turn i = -1)
    (hstep : ∀ i, C.heading (i + 1) =
      hexHeadingTurn (C.heading i) (turn i))
    (hn : 3 ≤ n) (horient : HexBrickInteriorOnLeft C.heading) :
    (∑ i, turn i) = -6 := by
  apply hex_turnSum_eq_neg_six_of_interiorOnLeft
    C.heading turn hlegal hstep
  · simpa [HexAWBrickCycle.direction] using C.closed
  · simpa [HexAWBrickCycle.direction] using C.pos_injective
  · exact hn
  · exact horient

end StatMech.Universality
