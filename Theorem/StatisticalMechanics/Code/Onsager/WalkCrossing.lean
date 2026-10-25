/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.BaseCase
import Theorem.StatisticalMechanics.Code.Onsager.NoDoubleWind
import Instance.StatisticalMechanics.Code.Onsager.WalkCrossing


namespace StatMech.Onsager.WalkCrossing

open Finset

open StatMech.Onsager.BaseCase

open StatMech.Onsager.NoDoubleWind

variable {n : ℕ} [NeZero n]


theorem snd_step (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0) (k : Fin n) :
    (pos d (k + 1)).2 = (pos d k).2 + (stepOf (d k)).2 := by
  rw [pos_succ d hclosed k, Prod.snd_add]


theorem fst_step (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0) (k : Fin n) :
    (pos d (k + 1)).1 = (pos d k).1 + (stepOf (d k)).1 := by
  rw [pos_succ d hclosed k, Prod.fst_add]


theorem vert_x_const (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (k : Fin n) (hk : isVertEdge (d k)) :
    (pos d (k + 1)).1 = (pos d k).1 := by
  rw [fst_step d hclosed k]
  rcases hk with h | h <;> rw [h] <;> simp [stepOf]


theorem vert_y_step (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (k : Fin n) (hk : isVertEdge (d k)) :
    (pos d (k + 1)).2 = (pos d k).2 + 1 ∨ (pos d (k + 1)).2 = (pos d k).2 - 1 := by
  rw [snd_step d hclosed k]
  rcases hk with h | h <;> rw [h]
  · left; simp [stepOf]
  · right; change (pos d k).2 + (-1 : ℤ) = (pos d k).2 - 1; ring


theorem horiz_y_const (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (k : Fin n) (hk : isHorizEdge (d k)) :
    (pos d (k + 1)).2 = (pos d k).2 := by
  rw [snd_step d hclosed k]
  rcases hk with h | h <;> rw [h] <;> simp [stepOf]


theorem horiz_x_step (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (k : Fin n) (hk : isHorizEdge (d k)) :
    (pos d (k + 1)).1 = (pos d k).1 + 1 ∨ (pos d (k + 1)).1 = (pos d k).1 - 1 := by
  rw [fst_step d hclosed k]
  rcases hk with h | h <;> rw [h]
  · left; simp [stepOf]
  · right; change (pos d k).1 + (-1 : ℤ) = (pos d k).1 - 1; ring


theorem stepOf_snd (w : Fin 4) : (stepOf w).2 = 0 ∨ (stepOf w).2 = 1 ∨ (stepOf w).2 = -1 := by
  fin_cases w <;> simp [stepOf]


theorem stepOf_fst (w : Fin 4) : (stepOf w).1 = 0 ∨ (stepOf w).1 = 1 ∨ (stepOf w).1 = -1 := by
  fin_cases w <;> simp [stepOf]


theorem snd_step_bound (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0) (k : Fin n) :
    (pos d (k + 1)).2 = (pos d k).2 ∨ (pos d (k + 1)).2 = (pos d k).2 + 1 ∨
      (pos d (k + 1)).2 = (pos d k).2 - 1 := by
  have h := stepOf_snd (d k)
  rw [snd_step d hclosed k]; omega


end StatMech.Onsager.WalkCrossing
