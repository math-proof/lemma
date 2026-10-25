/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/NoDoubleWind2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.NoDoubleWind


namespace StatMech.Onsager.NoDoubleWind2

open Finset

open StatMech.Onsager.BaseCase

open StatMech.Onsager.NoDoubleWind

variable {n : ℕ} [NeZero n]


theorem xco_succ (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0) (k : Fin n) :
    (pos d (k + 1)).1 = (pos d k).1 + (stepOf (d k)).1 := by
  rw [pos_succ d hclosed k]; rfl


theorem yco_succ (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0) (k : Fin n) :
    (pos d (k + 1)).2 = (pos d k).2 + (stepOf (d k)).2 := by
  rw [pos_succ d hclosed k]; rfl


theorem xstep_cases (w : Fin 4) :
    (w = 0 ∧ (stepOf w).1 = 1) ∨ (w = 2 ∧ (stepOf w).1 = -1) ∨
    ((w = 1 ∨ w = 3) ∧ (stepOf w).1 = 0) := by
  fin_cases w <;> simp [stepOf]


theorem ystep_cases (w : Fin 4) :
    (w = 1 ∧ (stepOf w).2 = 1) ∨ (w = 3 ∧ (stepOf w).2 = -1) ∨
    ((w = 0 ∨ w = 2) ∧ (stepOf w).2 = 0) := by
  fin_cases w <;> simp [stepOf]


theorem maxx_no_E_out (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0) (k : Fin n)
    (hmax : ∀ j : Fin n, (pos d j).1 ≤ (pos d k).1) : d k ≠ 0 := by
  intro hE
  have hs := xco_succ d hclosed k
  have hx1 : (stepOf (d k)).1 = 1 := by rw [hE]; rfl
  rw [hx1] at hs
  have := hmax (k + 1)
  omega


theorem maxx_no_W_in (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0) (k : Fin n)
    (hmax : ∀ j : Fin n, (pos d j).1 ≤ (pos d k).1) : d (k - 1) ≠ 2 := by
  intro hW
  have hs := xco_succ d hclosed (k - 1)
  rw [sub_add_cancel] at hs
  have hx1 : (stepOf (d (k - 1))).1 = -1 := by rw [hW]; rfl
  rw [hx1] at hs
  have := hmax (k - 1)
  omega


theorem miny_no_S_out (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0) (k : Fin n)
    (hmin : ∀ j : Fin n, (pos d k).2 ≤ (pos d j).2) : d k ≠ 3 := by
  intro hS
  have hs := yco_succ d hclosed k
  have hy1 : (stepOf (d k)).2 = -1 := by rw [hS]; rfl
  rw [hy1] at hs
  have := hmin (k + 1)
  omega

theorem miny_no_N_in (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0) (k : Fin n)
    (hmin : ∀ j : Fin n, (pos d k).2 ≤ (pos d j).2) : d (k - 1) ≠ 1 := by
  intro hN
  have hs := yco_succ d hclosed (k - 1)
  rw [sub_add_cancel] at hs
  have hy1 : (stepOf (d (k - 1))).2 = 1 := by rw [hN]; rfl
  rw [hy1] at hs
  have := hmin (k - 1)
  omega


end StatMech.Onsager.NoDoubleWind2
