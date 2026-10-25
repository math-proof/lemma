/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitWindingGeometry.Part10
import Def.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonEmbedding.Part2


namespace StatMech.FrontierD

open StatMech.Onsager

open StatMech.Onsager.BaseCase

noncomputable section

theorem fkRectRibbonCellResidueEmbed_normalize
    {M : ℕ} (hM : 0 < M) (i : Fin M) (o : Int) :
    fkRectRibbonCellResidueEmbed M
        (fkRectRibbonNormalizeCell hM i o) =
      (((8 * i.val : Nat) : Int) + o : ZMod (8 * M)) := by
  let z : Int := (i.val : Int) + o / 8
  have hM0 : (M : Int) ≠ 0 := by exact_mod_cast (ne_of_gt hM)
  have h80 : (8 : Int) ≠ 0 := by norm_num
  have hrM : ((z.natMod M : Nat) : Int) = z % (M : Int) := by
    unfold Int.natMod
    rw [Int.toNat_of_nonneg (Int.emod_nonneg z hM0)]
  have hr8 : ((o.natMod 8 : Nat) : Int) = o % 8 := by
    unfold Int.natMod
    rw [Int.toNat_of_nonneg (Int.emod_nonneg o h80)]
  simp only [fkRectRibbonCellResidueEmbed, fkRectRibbonNormalizeCell]
  rw [← Int.cast_natCast]
  rw [← Int.cast_add]
  change (((8 * (fkRectIntModFin hM
      ((i.val : Int) + o / 8)).val +
      (fkRectIntModFin (show 0 < 8 by decide) o).val : Nat) : Int) :
        ZMod (8 * M)) = _
  apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr
  refine ⟨z / (M : Int), ?_⟩
  simp only [fkRectIntModFin, Fin.val_mk]
  dsimp only [z] at hrM
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  rw [hrM, hr8]
  have hz := Int.emod_add_ediv z (M : Int)
  have ho := Int.emod_add_ediv o 8
  dsimp only [z] at hz ⊢
  linear_combination -8 * hz - ho

@[simp] theorem fkRectRibbonNormalizeCell_slot
    {M : ℕ} (hM : 0 < M) (i : Fin M) (r : Fin 8) :
    fkRectRibbonNormalizeCell hM i (r.val : Int) = (i, r) := by
  fin_cases r <;>
    apply Prod.ext <;>
    apply Fin.ext <;>
    simp [fkRectRibbonNormalizeCell, fkRectIntModFin, Int.natMod,
      Int.emod_eq_of_lt, i.isLt]

@[simp] theorem fkRectRibbonNormalizeCell_slot_add_eight
    {M : ℕ} (hM : 0 < M) (i : Fin M) (r : Fin 8) :
    fkRectRibbonNormalizeCell hM i (8 + r.val : Int) =
      (finitePeriodicSucc hM i, r) := by
  have hdiv : (8 + (r.val : Int)) / 8 = 1 := by
    omega
  apply Prod.ext
  · apply Fin.ext
    simp only [fkRectRibbonNormalizeCell, hdiv, Int.reduceAdd, Prod.fst]
    simp only [fkRectIntModFin, Fin.val_mk, Int.natMod,
      finitePeriodicSucc]
    rw [Int.toNat_emod (by omega) (by omega)]
    norm_num
  · fin_cases r <;>
      apply Fin.ext <;>
      norm_num [fkRectRibbonNormalizeCell, fkRectIntModFin, Int.natMod,
        Int.toNat]

@[simp] theorem fkRectRibbonNormalizeCell_neg_one
    {M : ℕ} (hM : 0 < M) (i : Fin M) :
    fkRectRibbonNormalizeCell hM i (-1) =
      (SixVertexArrows.cyclicPred hM i, (7 : Fin 8)) := by
  apply Prod.ext
  · exact congrArg id (fkRectIntModFin_natCast_sub_one hM i)
  · apply Fin.ext
    norm_num [fkRectRibbonNormalizeCell, fkRectIntModFin, Int.natMod,
      Int.toNat]

@[simp] theorem fkRectRibbonNormalizeCell_zero
    {M : ℕ} (hM : 0 < M) (i : Fin M) :
    fkRectRibbonNormalizeCell hM i 0 = (i, (0 : Fin 8)) := by
  simpa using fkRectRibbonNormalizeCell_slot hM i (0 : Fin 8)

@[simp] theorem fkRectRibbonNormalizeCell_one
    {M : ℕ} (hM : 0 < M) (i : Fin M) :
    fkRectRibbonNormalizeCell hM i 1 = (i, (1 : Fin 8)) := by
  simpa using fkRectRibbonNormalizeCell_slot hM i (1 : Fin 8)

@[simp] theorem fkRectRibbonNormalizeCell_two
    {M : ℕ} (hM : 0 < M) (i : Fin M) :
    fkRectRibbonNormalizeCell hM i 2 = (i, (2 : Fin 8)) := by
  simpa using fkRectRibbonNormalizeCell_slot hM i (2 : Fin 8)

@[simp] theorem fkRectRibbonNormalizeCell_three
    {M : ℕ} (hM : 0 < M) (i : Fin M) :
    fkRectRibbonNormalizeCell hM i 3 = (i, (3 : Fin 8)) := by
  simpa using fkRectRibbonNormalizeCell_slot hM i (3 : Fin 8)

@[simp] theorem fkRectRibbonNormalizeCell_four
    {M : ℕ} (hM : 0 < M) (i : Fin M) :
    fkRectRibbonNormalizeCell hM i 4 = (i, (4 : Fin 8)) := by
  simpa using fkRectRibbonNormalizeCell_slot hM i (4 : Fin 8)

@[simp] theorem fkRectRibbonNormalizeCell_five
    {M : ℕ} (hM : 0 < M) (i : Fin M) :
    fkRectRibbonNormalizeCell hM i 5 = (i, (5 : Fin 8)) := by
  simpa using fkRectRibbonNormalizeCell_slot hM i (5 : Fin 8)

@[simp] theorem fkRectRibbonNormalizeCell_six
    {M : ℕ} (hM : 0 < M) (i : Fin M) :
    fkRectRibbonNormalizeCell hM i 6 = (i, (6 : Fin 8)) := by
  simpa using fkRectRibbonNormalizeCell_slot hM i (6 : Fin 8)

@[simp] theorem fkRectRibbonNormalizeCell_seven
    {M : ℕ} (hM : 0 < M) (i : Fin M) :
    fkRectRibbonNormalizeCell hM i 7 = (i, (7 : Fin 8)) := by
  simpa using fkRectRibbonNormalizeCell_slot hM i (7 : Fin 8)

@[simp] theorem fkRectRibbonNormalizeCell_eight
    {M : ℕ} (hM : 0 < M) (i : Fin M) :
    fkRectRibbonNormalizeCell hM i 8 =
      (finitePeriodicSucc hM i, (0 : Fin 8)) := by
  simpa using fkRectRibbonNormalizeCell_slot_add_eight hM i (0 : Fin 8)

@[simp] theorem fkRectRibbonNormalizeCell_nine
    {M : ℕ} (hM : 0 < M) (i : Fin M) :
    fkRectRibbonNormalizeCell hM i 9 =
      (finitePeriodicSucc hM i, (1 : Fin 8)) := by
  simpa using fkRectRibbonNormalizeCell_slot_add_eight hM i (1 : Fin 8)


end
end StatMech.FrontierD
