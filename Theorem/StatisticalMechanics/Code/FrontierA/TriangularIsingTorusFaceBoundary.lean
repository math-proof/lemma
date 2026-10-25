/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFaceBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusBaseSpin
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusFaceBoundary
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Onsager


theorem triangularFaceBoundaryCoeff_reverse
    {L : Nat} (lower upper : (ZMod L × ZMod L) -> ZMod 2)
    (d : triangularTorusDart L) :
    triangularFaceBoundaryCoeff lower upper
        (triangularTorusDartReverse L d) =
      -triangularFaceBoundaryCoeff lower upper d := by
  rcases d with ⟨p, a⟩
  rcases p with ⟨x, y⟩
  fin_cases a <;>
    simp [triangularFaceBoundaryCoeff, triangularFaceEastCoeff,
      triangularFaceNorthCoeff, triangularFaceDiagonalCoeff,
      triangularTorusDartReverse, triangularTorusDirectionReverse,
      triangularTorusDirectionStep] <;> ring


theorem triangularFaceBoundaryCoeff_divergence
    {L : Nat} (lower upper : (ZMod L × ZMod L) -> ZMod 2)
    (p : ZMod L × ZMod L) :
    (∑ a : Fin 6, triangularFaceBoundaryCoeff lower upper (p, a)) = 0 := by
  rw [show (Finset.univ : Finset (Fin 6)) = {0, 1, 2, 3, 4, 5} by decide]
  simp [triangularFaceBoundaryCoeff, triangularFaceEastCoeff,
    triangularFaceNorthCoeff, triangularFaceDiagonalCoeff]
  ring

theorem triangularFaceCoeff_cast_mod_two (a b : ZMod 2) :
    (((a.val : Int) - (b.val : Int) : Int) : ZMod 2) = a + b := by
  rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast,
    ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  rw [sub_eq_add_neg, CharTwo.neg_eq]

theorem triangularFaceEastCoeff_cast_mod_two
    {L : Nat} (lower upper : (ZMod L × ZMod L) -> ZMod 2)
    (p : ZMod L × ZMod L) :
    (triangularFaceEastCoeff lower upper p : ZMod 2) =
      lower p + upper (p.1, p.2 - 1) := by
  rw [triangularFaceEastCoeff]
  exact triangularFaceCoeff_cast_mod_two _ _

theorem triangularFaceNorthCoeff_cast_mod_two
    {L : Nat} (lower upper : (ZMod L × ZMod L) -> ZMod 2)
    (p : ZMod L × ZMod L) :
    (triangularFaceNorthCoeff lower upper p : ZMod 2) =
      lower (p.1 - 1, p.2) + upper p := by
  rw [triangularFaceNorthCoeff]
  exact triangularFaceCoeff_cast_mod_two _ _

theorem triangularFaceDiagonalCoeff_cast_mod_two
    {L : Nat} (lower upper : (ZMod L × ZMod L) -> ZMod 2)
    (p : ZMod L × ZMod L) :
    (triangularFaceDiagonalCoeff lower upper p : ZMod 2) =
      lower p + upper p := by
  rw [triangularFaceDiagonalCoeff]
  rw [triangularFaceCoeff_cast_mod_two, add_comm]


theorem triangularFaceCoeff_eq_zero_of_cast_eq_zero
    (a b : ZMod 2)
    (h : ((((a.val : Int) - (b.val : Int) : Int)) : ZMod 2) = 0) :
    (a.val : Int) - b.val = 0 := by
  have hab : a = b := by
    have h' : a - b = 0 := by
      simpa only [Int.cast_sub, Int.cast_natCast,
        ZMod.natCast_zmod_val] using h
    exact sub_eq_zero.mp h'
  rw [hab, sub_self]


theorem triangularFaceCoeff_ne_zero_of_cast_ne_zero
    (a b : ZMod 2)
    (h : ((((a.val : Int) - (b.val : Int) : Int)) : ZMod 2) ≠ 0) :
    (a.val : Int) - b.val ≠ 0 := by
  exact fun hz => h (by simpa only [hz, Int.cast_zero])

theorem triangularFaceEastCoeff_eq_zero_of_cast_eq_zero
    {L : Nat} (lower upper : (ZMod L × ZMod L) -> ZMod 2)
    (p : ZMod L × ZMod L)
    (h : (triangularFaceEastCoeff lower upper p : ZMod 2) = 0) :
    triangularFaceEastCoeff lower upper p = 0 := by
  apply triangularFaceCoeff_eq_zero_of_cast_eq_zero _ _
  simpa only [triangularFaceEastCoeff] using h

theorem triangularFaceNorthCoeff_eq_zero_of_cast_eq_zero
    {L : Nat} (lower upper : (ZMod L × ZMod L) -> ZMod 2)
    (p : ZMod L × ZMod L)
    (h : (triangularFaceNorthCoeff lower upper p : ZMod 2) = 0) :
    triangularFaceNorthCoeff lower upper p = 0 := by
  apply triangularFaceCoeff_eq_zero_of_cast_eq_zero _ _
  simpa only [triangularFaceNorthCoeff] using h

theorem triangularFaceDiagonalCoeff_eq_zero_of_cast_eq_zero
    {L : Nat} (lower upper : (ZMod L × ZMod L) -> ZMod 2)
    (p : ZMod L × ZMod L)
    (h : (triangularFaceDiagonalCoeff lower upper p : ZMod 2) = 0) :
    triangularFaceDiagonalCoeff lower upper p = 0 := by
  apply triangularFaceCoeff_eq_zero_of_cast_eq_zero _ _
  simpa only [triangularFaceDiagonalCoeff] using h


theorem triangularFaceBoundary_horizontal_seam_sum
    {L : Nat} [NeZero L]
    (lower upper : (ZMod L × ZMod L) -> ZMod 2) (x : ZMod L) :
    (∑ y : ZMod L,
      (triangularFaceEastCoeff lower upper (x, y) +
        triangularFaceDiagonalCoeff lower upper (x, y))) = 0 := by
  simp_rw [triangularFaceEastCoeff, triangularFaceDiagonalCoeff]
  simp_rw [show forall y : ZMod L,
      ((lower (x, y)).val : Int) - (upper (x, y - 1)).val +
          ((upper (x, y)).val - (lower (x, y)).val) =
        (upper (x, y)).val - (upper (x, y - 1)).val by
    intro y
    ring]
  rw [Finset.sum_sub_distrib]
  have hshift :
      (∑ y : ZMod L, ((upper (x, y - 1)).val : Int)) =
        ∑ y : ZMod L, ((upper (x, y)).val : Int) := by
    simpa [sub_eq_add_neg] using
      (Equiv.sum_comp (Equiv.addRight (-1 : ZMod L))
        (fun y : ZMod L => ((upper (x, y)).val : Int)))
  rw [hshift, sub_self]


theorem triangularFaceBoundary_vertical_seam_sum
    {L : Nat} [NeZero L]
    (lower upper : (ZMod L × ZMod L) -> ZMod 2) (y : ZMod L) :
    (∑ x : ZMod L,
      (triangularFaceNorthCoeff lower upper (x, y) +
        triangularFaceDiagonalCoeff lower upper (x, y))) = 0 := by
  simp_rw [triangularFaceNorthCoeff, triangularFaceDiagonalCoeff]
  simp_rw [show forall x : ZMod L,
      ((lower (x - 1, y)).val : Int) - (upper (x, y)).val +
          ((upper (x, y)).val - (lower (x, y)).val) =
        (lower (x - 1, y)).val - (lower (x, y)).val by
    intro x
    ring]
  rw [Finset.sum_sub_distrib]
  have hshift :
      (∑ x : ZMod L, ((lower (x - 1, y)).val : Int)) =
        ∑ x : ZMod L, ((lower (x, y)).val : Int) := by
    simpa [sub_eq_add_neg] using
      (Equiv.sum_comp (Equiv.addRight (-1 : ZMod L))
        (fun x : ZMod L => ((lower (x, y)).val : Int)))
  rw [hshift, sub_self]

end StatMech.FrontierA
