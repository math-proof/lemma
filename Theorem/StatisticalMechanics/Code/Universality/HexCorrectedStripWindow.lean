/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripExit
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
import Theorem.StatisticalMechanics.Code.Onsager.PeriodicTurnClosure.Part9
import Def.StatisticalMechanics.Code.Universality.HexCorrectedStripWindow


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

open StatMech.Onsager

noncomputable section

@[simp] theorem hexCSHeadingFin_zero : hexCSHeadingFin 0 = 0 := by
  apply (ZMod.finEquiv 6).injective
  simp [hexCSHeadingFin]

@[simp] theorem hexCSHeadingFin_one : hexCSHeadingFin 1 = 1 := by
  apply (ZMod.finEquiv 6).injective
  simp [hexCSHeadingFin]

theorem hexCSHeadingFin_add (h k : ℤ) :
    hexCSHeadingFin (h + k) = hexCSHeadingFin h + hexCSHeadingFin k := by
  apply (ZMod.finEquiv 6).injective
  simp [hexCSHeadingFin]

theorem hexCSHeadingFin_dvd (h : ℤ) :
    (6 : ℤ) ∣ h - (hexCSHeadingFin h).val := by
  have hz : hexCSHeadingFin h = (h : ZMod 6) :=
    (ZMod.finEquiv 6).apply_symm_apply _
  have hvn : (hexCSHeadingFin h).val = (h : ZMod 6).val :=
    congrArg Fin.val hz
  have hvcast : (((h : ZMod 6).val : ℕ) : ℤ) = h % 6 :=
    ZMod.val_intCast (n := 6) h
  have hv : ((hexCSHeadingFin h).val : ℤ) = h % 6 :=
    (congrArg (fun n : ℕ => (n : ℤ)) hvn).trans hvcast
  refine ⟨h / 6, ?_⟩
  rw [hv, Int.emod_def]
  ring

theorem hexCSHeadingFin_unit (h : ℤ) :
    hexUnit h = hexUnit (hexCSHeadingFin h).val := by
  exact (hexUnit_eq_iff_mod _ _).2 (hexCSHeadingFin_dvd h)

theorem hexCSHeadingFin_turn (h t : ℤ) (ht : t = 1 ∨ t = -1) :
    hexCSHeadingFin (h + t) =
      hexHeadingTurn (hexCSHeadingFin h) t := by
  rcases ht with rfl | rfl
  · rw [hexHeadingTurn, if_pos rfl, hexCSHeadingFin_add]
    simp
  · rw [hexHeadingTurn, if_neg (by norm_num), hexCSHeadingFin_add]
    apply (ZMod.finEquiv 6).injective
    simp [hexCSHeadingFin, sub_eq_add_neg]


end
end StatMech.Universality
