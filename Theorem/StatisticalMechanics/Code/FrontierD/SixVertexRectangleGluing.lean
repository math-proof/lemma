/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleGluing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleSymmetry.Part3
open Finset


namespace StatMech.FrontierD

@[simp] theorem finAddCases_zero_succ {m n : ℕ} {α : Type*}
    (left : Fin (m + 1) → α) (right : Fin n → α) :
    Fin.addCases (m := m + 1) (n := n) left right 0 = left 0 := by
  change Fin.addCases left right (Fin.castAdd n (0 : Fin (m + 1))) = left 0
  rw [Fin.addCases_left]

@[simp] theorem finAddCases_last_succ {m n : ℕ} {α : Type*}
    (left : Fin m → α) (right : Fin (n + 1) → α) :
    Fin.addCases (m := m) (n := n + 1) left right (Fin.last (m + n)) =
      right (Fin.last n) := by
  rw [← Fin.natAdd_last]
  exact Fin.addCases_right _

@[simp] theorem finCastAdd_castSucc {w : ℕ} (i : Fin w) :
    (Fin.castAdd w i).castSucc = Fin.castAdd (w + 1) i := by
  ext
  rfl

@[simp] theorem finCastAdd_castSucc_succ {n : ℕ} (i : Fin n) :
    (Fin.castAdd (n + 1) i.castSucc).succ = Fin.castAdd (n + 2) i.succ := by
  ext
  rfl

@[simp] theorem finCastAdd_last_succ {n : ℕ} :
    (Fin.castAdd (n + 1) (Fin.last n)).succ =
      Fin.natAdd (n + 1) (0 : Fin (n + 2)) := by
  ext
  simp

@[simp] theorem finAddCases_addNat_self {n : ℕ} {α : Type*}
    (left right : Fin n → α) (i : Fin n) :
    Fin.addCases (m := n) (n := n) left right (Fin.addNat i n) = right i := by
  rw [show Fin.addNat i n = Fin.natAdd n i by
    ext
    simp [Fin.addNat, Fin.natAdd, Nat.add_comm], Fin.addCases_right]

theorem finAddNat_eq_natAdd_self {n : ℕ} (i : Fin n) :
    Fin.addNat i n = Fin.natAdd n i := by
  ext
  simp [Fin.addNat, Fin.natAdd, Nat.add_comm]

@[simp] theorem finAddCases_addNat_castSucc_self {n : ℕ} {α : Type*}
    (left : Fin n → α) (right : Fin (n + 1) → α) (i : Fin n) :
    Fin.addCases (m := n) (n := n + 1) left right
        (Fin.addNat i n).castSucc = right i.castSucc := by
  rw [show (Fin.addNat i n).castSucc = Fin.natAdd n i.castSucc by
    ext
    simp [Fin.addNat, Fin.natAdd, Nat.add_comm], Fin.addCases_right]

@[simp] theorem finAddCases_addNat_succ_self {n : ℕ} {α : Type*}
    (left : Fin n → α) (right : Fin (n + 1) → α) (i : Fin n) :
    Fin.addCases (m := n) (n := n + 1) left right
        (Fin.addNat i n).succ = right i.succ := by
  rw [show (Fin.addNat i n).succ = Fin.natAdd n i.succ by
    ext
    simp [Fin.addNat, Fin.natAdd, Nat.add_comm]
    omega, Fin.addCases_right]


end StatMech.FrontierD
