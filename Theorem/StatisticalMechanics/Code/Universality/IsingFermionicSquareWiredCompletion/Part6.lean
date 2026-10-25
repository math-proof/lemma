/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part39
import Mathlib.Logic.Equiv.Fintype
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion.Part6


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem perm_conjugate_involutive {X : Type*}
    (sigma B : Equiv.Perm X) (hB : Function.Involutive B) :
    Function.Involutive (sigma * B * sigma.symm) := by
  intro x
  simp only [Equiv.Perm.mul_apply]
  rw [sigma.symm_apply_apply, hB, sigma.apply_symm_apply]

theorem fkIsingSquareWiredBondMate_involutive (n : Nat) (hn : 0 < n) :
    Function.Involutive (fkIsingSquareWiredBondMate n hn) := by
  exact perm_conjugate_involutive
    (fkIsingSquareWiredShiftDartEquiv n hn)
    (fkIsingSquareBondMateEquiv n hn)
    (fkIsingSquareBondMate_involutive n hn)

theorem fkIsingSquareWiredBondMate_ne (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareWiredBondMate n hn d ≠ d := by
  intro h
  let sigma := fkIsingSquareWiredShiftDartEquiv n hn
  let B := fkIsingSquareBondMateEquiv n hn
  have h' := congrArg sigma.symm h
  simp only [fkIsingSquareWiredBondMate, fkIsingSquareWiredBondMateEquiv,
    Equiv.Perm.mul_apply] at h'
  have : B (sigma.symm d) = sigma.symm d := by simpa [sigma, B] using h'
  exact fkIsingSquareBondMate_ne n hn (sigma.symm d) this

theorem fkIsingSquareBondMate_wired_bottom (n : Nat) (hn : 0 < n) :
    fkIsingSquareBondMate n hn
        (fkIsingSquareWiredBoundaryDart n hn .bottom) =
      fkIsingSquareWiredBoundaryDart n hn
        (.west ⟨0, by omega⟩) := by
  simp only [fkIsingSquareWiredBoundaryDart, fkIsingSquareBondMate,
    fkIsingSquareDirectionDart_endpoint, fkIsingSquareDirectionDart_direction,
    fkIsingSquareDirectionDart_turn]
  simp [fkIsingSquarePreviousDirection, fkIsingSquareDirectionAvailable,
    fkIsingSquareMarkedA, fkIsingSquareLeftVerticalLower,
    fkIsingSquareDirectionDart]

theorem fkIsingSquareBondMate_wired_west_zero (n : Nat) (hn : 0 < n) :
    fkIsingSquareBondMate n hn
        (fkIsingSquareWiredBoundaryDart n hn (.west ⟨0, by omega⟩)) =
      fkIsingSquareWiredBoundaryDart n hn .bottom := by
  rw [← fkIsingSquareBondMate_wired_bottom n hn]
  exact fkIsingSquareBondMate_involutive n hn _

theorem fkIsingSquareBondMate_wired_west_succ (n : Nat) (hn : 0 < n)
    (k : Fin (2 * n)) (hk : k.val ≠ 0) :
    fkIsingSquareBondMate n hn
        (fkIsingSquareWiredBoundaryDart n hn (.west k)) =
      fkIsingSquareWiredBoundaryDart n hn
        (.north ⟨k.val - 1, by omega⟩) := by
  have hkpos : 0 < k.val := Nat.pos_of_ne_zero hk
  have hsouth : -(n : Int) < -(n : Int) + (k.val : Int) := by
    have hkpos' : (0 : Int) < (k.val : Int) := by exact_mod_cast hkpos
    omega
  have hu : fkIsingSquareLeftVerticalLower n hn k =
      fkIsingSquareLeftVerticalUpper n hn ⟨k.val - 1, by omega⟩ := by
    apply Subtype.ext
    funext i
    fin_cases i
    · simp [fkIsingSquareLeftVerticalLower,
        fkIsingSquareLeftVerticalUpper]
    · simp only [fkIsingSquareLeftVerticalLower,
        fkIsingSquareLeftVerticalUpper]
      rw [Nat.cast_sub (by omega : 1 ≤ k.val)]
      push_cast
      ring
  have hw : ¬ fkIsingSquareDirectionAvailable n
      (fkIsingSquareLeftVerticalLower n hn k) .west := by
    simp [fkIsingSquareDirectionAvailable, fkIsingSquareLeftVerticalLower]
  have hs : fkIsingSquareDirectionAvailable n
      (fkIsingSquareLeftVerticalLower n hn k) .south := by
    simpa [fkIsingSquareDirectionAvailable,
      fkIsingSquareLeftVerticalLower] using hsouth
  simp only [fkIsingSquareWiredBoundaryDart, fkIsingSquareBondMate,
    fkIsingSquareDirectionDart_endpoint, fkIsingSquareDirectionDart_direction,
    fkIsingSquareDirectionDart_turn]
  simp only [fkIsingSquareNextDirection, hw, hs, ↓reduceIte]
  exact fkIsingSquareDirectionDart_endpoint_congr n hu .south _ _ _

theorem fkIsingSquareBondMate_wired_north_not_last
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n))
    (hk : k.val + 1 < 2 * n) :
    fkIsingSquareBondMate n hn
        (fkIsingSquareWiredBoundaryDart n hn (.north k)) =
      fkIsingSquareWiredBoundaryDart n hn
        (.west ⟨k.val + 1, hk⟩) := by
  have hnorth : -(n : Int) + (k.val : Int) + 1 < (n : Int) := by
    have hk' : (k.val : Int) + 1 < 2 * (n : Int) := by exact_mod_cast hk
    omega
  have hu : fkIsingSquareLeftVerticalUpper n hn k =
      fkIsingSquareLeftVerticalLower n hn ⟨k.val + 1, hk⟩ := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [fkIsingSquareLeftVerticalLower,
        fkIsingSquareLeftVerticalUpper] <;> ring
  have hw : ¬ fkIsingSquareDirectionAvailable n
      (fkIsingSquareLeftVerticalUpper n hn k) .west := by
    simp [fkIsingSquareDirectionAvailable, fkIsingSquareLeftVerticalUpper]
  have hnorth' : fkIsingSquareDirectionAvailable n
      (fkIsingSquareLeftVerticalUpper n hn k) .north := by
    simpa [fkIsingSquareDirectionAvailable,
      fkIsingSquareLeftVerticalUpper] using hnorth
  simp only [fkIsingSquareWiredBoundaryDart, fkIsingSquareBondMate,
    fkIsingSquareDirectionDart_endpoint, fkIsingSquareDirectionDart_direction,
    fkIsingSquareDirectionDart_turn]
  simp only [fkIsingSquarePreviousDirection, hw, hnorth', ↓reduceIte]
  exact fkIsingSquareDirectionDart_endpoint_congr n hu .north _ _ _

theorem fkIsingSquareBondMate_wired_north_last
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n))
    (hk : ¬k.val + 1 < 2 * n) :
    fkIsingSquareBondMate n hn
        (fkIsingSquareWiredBoundaryDart n hn (.north k)) =
      fkIsingSquareWiredBoundaryDart n hn .top := by
  have hlast : k.val = 2 * n - 1 := by omega
  have htop : -(n : Int) + (k.val : Int) + 1 = (n : Int) := by
    rw [hlast, Nat.cast_sub (by omega : 1 ≤ 2 * n)]
    push_cast
    ring
  simp only [fkIsingSquareWiredBoundaryDart, fkIsingSquareBondMate,
    fkIsingSquareDirectionDart_endpoint, fkIsingSquareDirectionDart_direction,
    fkIsingSquareDirectionDart_turn]
  simp [fkIsingSquarePreviousDirection, fkIsingSquareDirectionAvailable,
    fkIsingSquareLeftVerticalUpper, fkIsingSquareMarkedB,
    fkIsingSquareDirectionDart, htop]

theorem fkIsingSquareBondMate_wired_top (n : Nat) (hn : 0 < n) :
    fkIsingSquareBondMate n hn
        (fkIsingSquareWiredBoundaryDart n hn .top) =
      fkIsingSquareWiredBoundaryDart n hn
        (.north ⟨2 * n - 1, by omega⟩) := by
  let k : Fin (2 * n) := ⟨2 * n - 1, by omega⟩
  have hk : ¬k.val + 1 < 2 * n := by simp [k]; omega
  rw [← fkIsingSquareBondMate_wired_north_last n hn k hk]
  exact fkIsingSquareBondMate_involutive n hn _

@[simp] theorem fkIsingSquareWiredShiftDartEquiv_apply_boundary
    (n : Nat) (hn : 0 < n) (i : FKIsingSquareWiredBoundaryDartIndex n) :
    fkIsingSquareWiredShiftDartEquiv n hn
        (fkIsingSquareWiredBoundaryDart n hn i) =
      fkIsingSquareWiredBoundaryDart n hn
        (fkIsingSquareWiredShift n hn i) := by
  exact Equiv.Perm.viaFintypeEmbedding_apply_image
    (fkIsingSquareWiredShiftEquiv n hn)
    (fkIsingSquareWiredBoundaryEmbedding n hn) i

@[simp] theorem fkIsingSquareWiredShiftDartEquiv_symm_apply_boundary
    (n : Nat) (hn : 0 < n) (i : FKIsingSquareWiredBoundaryDartIndex n) :
    (fkIsingSquareWiredShiftDartEquiv n hn).symm
        (fkIsingSquareWiredBoundaryDart n hn i) =
      fkIsingSquareWiredBoundaryDart n hn
        (fkIsingSquareWiredShiftInv n hn i) := by
  apply (fkIsingSquareWiredShiftDartEquiv n hn).injective
  rw [(fkIsingSquareWiredShiftDartEquiv n hn).apply_symm_apply]
  rw [fkIsingSquareWiredShiftDartEquiv_apply_boundary]
  rw [fkIsingSquareWiredShift_right_inv]

@[simp] theorem fkIsingSquareWiredBondMate_bottom (n : Nat) (hn : 0 < n) :
    fkIsingSquareWiredBondMate n hn
        (fkIsingSquareWiredBoundaryDart n hn .bottom) =
      fkIsingSquareWiredBoundaryDart n hn .top := by
  simp only [fkIsingSquareWiredBondMate, fkIsingSquareWiredBondMateEquiv,
    Equiv.Perm.mul_apply,
    fkIsingSquareWiredShiftDartEquiv_symm_apply_boundary,
    fkIsingSquareWiredShiftInv]
  change fkIsingSquareWiredShiftDartEquiv n hn
      (fkIsingSquareBondMate n hn
        (fkIsingSquareWiredBoundaryDart n hn .bottom)) = _
  rw [fkIsingSquareBondMate_wired_bottom]
  rw [fkIsingSquareWiredShiftDartEquiv_apply_boundary]
  simp [fkIsingSquareWiredShift]

@[simp] theorem fkIsingSquareWiredBondMate_top (n : Nat) (hn : 0 < n) :
    fkIsingSquareWiredBondMate n hn
        (fkIsingSquareWiredBoundaryDart n hn .top) =
      fkIsingSquareWiredBoundaryDart n hn .bottom := by
  rw [← fkIsingSquareWiredBondMate_bottom n hn]
  exact fkIsingSquareWiredBondMate_involutive n hn _

@[simp] theorem fkIsingSquareWiredBondMate_west (n : Nat) (hn : 0 < n)
    (k : Fin (2 * n)) :
    fkIsingSquareWiredBondMate n hn
        (fkIsingSquareWiredBoundaryDart n hn (.west k)) =
      fkIsingSquareWiredBoundaryDart n hn (.north k) := by
  simp only [fkIsingSquareWiredBondMate, fkIsingSquareWiredBondMateEquiv,
    Equiv.Perm.mul_apply,
    fkIsingSquareWiredShiftDartEquiv_symm_apply_boundary,
    fkIsingSquareWiredShiftInv]
  change fkIsingSquareWiredShiftDartEquiv n hn
      (fkIsingSquareBondMate n hn
        (fkIsingSquareWiredBoundaryDart n hn (.north k))) = _
  by_cases hk : k.val + 1 < 2 * n
  · rw [fkIsingSquareBondMate_wired_north_not_last n hn k hk]
    rw [fkIsingSquareWiredShiftDartEquiv_apply_boundary]
    simp [fkIsingSquareWiredShift]
  · rw [fkIsingSquareBondMate_wired_north_last n hn k hk]
    rw [fkIsingSquareWiredShiftDartEquiv_apply_boundary]
    simp only [fkIsingSquareWiredShift]
    have hlast : k.val = 2 * n - 1 := by omega
    congr 2
    apply Fin.ext
    exact hlast.symm

@[simp] theorem fkIsingSquareWiredBondMate_north (n : Nat) (hn : 0 < n)
    (k : Fin (2 * n)) :
    fkIsingSquareWiredBondMate n hn
        (fkIsingSquareWiredBoundaryDart n hn (.north k)) =
      fkIsingSquareWiredBoundaryDart n hn (.west k) := by
  rw [← fkIsingSquareWiredBondMate_west n hn k]
  exact fkIsingSquareWiredBondMate_involutive n hn _


end
end StatMech.Universality
