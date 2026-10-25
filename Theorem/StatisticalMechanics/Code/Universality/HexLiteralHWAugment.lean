/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Structure.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexHalfEdgeClose.Part3
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWAugment


namespace StatMech.Universality

open HexWalk


@[simp] theorem hlha_negCoord_x (p : HexReturnCoord) :
    (hlha_negCoord p).x = -p.x := rfl

@[simp] theorem hlha_negCoord_y (p : HexReturnCoord) :
    (hlha_negCoord p).y = -p.y := rfl

@[simp] theorem hlha_swapCoord_x (p : HexReturnCoord) :
    (hlha_swapCoord p).x = p.y := rfl

@[simp] theorem hlha_swapCoord_y (p : HexReturnCoord) :
    (hlha_swapCoord p).y = p.x := rfl

@[simp] theorem hlha_negCoord_zero :
    hlha_negCoord HexReturnCoord.zero = HexReturnCoord.zero := rfl

@[simp] theorem hlha_swapCoord_zero :
    hlha_swapCoord HexReturnCoord.zero = HexReturnCoord.zero := rfl

theorem hlha_negCoord_injective : Function.Injective hlha_negCoord := by
  intro p q h
  cases p
  cases q
  simp only [hlha_negCoord, HexReturnCoord.mk.injEq] at h ⊢
  omega

theorem hlha_swapCoord_injective : Function.Injective hlha_swapCoord := by
  intro p q h
  cases p
  cases q
  simp only [hlha_swapCoord, HexReturnCoord.mk.injEq] at h ⊢
  exact ⟨h.2, h.1⟩

theorem hlha_add_left_injective (q : HexReturnCoord) :
    Function.Injective q.add := by
  intro p r h
  cases q
  cases p
  cases r
  simp only [HexReturnCoord.add, HexReturnCoord.mk.injEq] at h ⊢
  omega

@[simp] theorem hlha_add_zero (q : HexReturnCoord) :
    q.add HexReturnCoord.zero = q := by
  cases q
  simp [HexReturnCoord.add, HexReturnCoord.zero]

@[simp] theorem hlha_zero_add (q : HexReturnCoord) :
    HexReturnCoord.zero.add q = q := by
  cases q
  simp [HexReturnCoord.add, HexReturnCoord.zero]

@[simp] theorem hlha_negCoord_add (p q : HexReturnCoord) :
    hlha_negCoord (p.add q) =
      (hlha_negCoord p).add (hlha_negCoord q) := by
  cases p
  cases q
  simp [hlha_negCoord, HexReturnCoord.add]
  constructor <;> omega

@[simp] theorem hlha_swapCoord_add (p q : HexReturnCoord) :
    hlha_swapCoord (p.add q) =
      (hlha_swapCoord p).add (hlha_swapCoord q) := by
  cases p
  cases q
  simp [hlha_swapCoord, HexReturnCoord.add]

theorem hlha_negCoord_turn (d : HexReturnCoord) {t : ℤ}
    (ht : t = 1 ∨ t = -1) :
    hlha_negCoord (d.turn t) = (hlha_negCoord d).turn t := by
  rcases d with ⟨x, y⟩
  rcases ht with rfl | rfl <;>
    simp [hlha_negCoord, HexReturnCoord.turn,
      HexReturnCoord.left, HexReturnCoord.right] <;> omega

theorem hlha_swapCoord_turn (d : HexReturnCoord) {t : ℤ}
    (ht : t = 1 ∨ t = -1) :
    hlha_swapCoord (d.turn t) =
      (hlha_swapCoord d).turn (-t) := by
  rcases d with ⟨x, y⟩
  rcases ht with rfl | rfl <;>
    simp [hlha_swapCoord, HexReturnCoord.turn,
      HexReturnCoord.left, HexReturnCoord.right]


end StatMech.Universality
