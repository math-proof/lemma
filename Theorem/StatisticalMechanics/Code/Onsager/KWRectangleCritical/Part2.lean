/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWRectangleCritical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.KWSpectralCritical
import Def.StatisticalMechanics.Code.Onsager.KWRectangleCritical.Part3


namespace StatMech.Onsager

open Matrix BigOperators

open scoped Matrix.Norms.L2Operator


theorem ons_rectDartBoundaryRank_tail_lt (M N : Nat)
    (d : ons_RectDart M N) (hd : ons_rectDartValid M N d)
    (htail : ons_rectDartValid M N (ons_rectTailDartEquiv M N d)) :
    ons_rectDartBoundaryRank M N (ons_rectTailDartEquiv M N d) <
      ons_rectDartBoundaryRank M N d := by
  rcases d with ⟨⟨x, y⟩, mu⟩
  fin_cases mu
  · simp [ons_rectTailDartEquiv_apply, ons_rectDirStep, ons_rectDartValid,
      ons_rectDartBoundaryRank] at hd htail ⊢
    have hx0 : x ≠ 0 := by
      intro hx
      subst x
      simp at htail
    have hxpos : 0 < x.val := by
      exact Nat.pos_of_ne_zero (fun h => hx0 (ZMod.val_eq_zero x |>.mp h))
    have hmod : 1 < M + 1 := by
      have := ZMod.val_lt x
      omega
    have hone : (1 : ZMod (M + 1)).val <= x.val := by
      letI : Fact (1 < M + 1) := ⟨hmod⟩
      simpa only [ZMod.val_one] using hxpos
    letI : Fact (1 < M + 1) := ⟨hmod⟩
    rw [ZMod.val_sub hone]
    rw [ZMod.val_one]
    omega
  · simp [ons_rectTailDartEquiv_apply, ons_rectDirStep, ons_rectDartValid,
      ons_rectDartBoundaryRank] at hd htail ⊢
    have hy0 : y ≠ 0 := by
      intro hy
      subst y
      simp at htail
    have hypos : 0 < y.val := by
      exact Nat.pos_of_ne_zero (fun h => hy0 (ZMod.val_eq_zero y |>.mp h))
    have hmod : 1 < N + 1 := by
      have := ZMod.val_lt y
      omega
    have hone : (1 : ZMod (N + 1)).val <= y.val := by
      letI : Fact (1 < N + 1) := ⟨hmod⟩
      simpa only [ZMod.val_one] using hypos
    letI : Fact (1 < N + 1) := ⟨hmod⟩
    rw [ZMod.val_sub hone]
    rw [ZMod.val_one]
    omega
  · simp [ons_rectTailDartEquiv_apply, ons_rectDirStep, ons_rectDartValid,
      ons_rectDartBoundaryRank] at hd htail ⊢
    have hxpos : 0 < x.val := by
      exact Nat.pos_of_ne_zero (fun h => hd (ZMod.val_eq_zero x |>.mp h))
    have hxlt : x.val < M := by
      by_contra h
      have hxM : x.val = M := by
        have := ZMod.val_lt x
        omega
      have hmod : 1 < M + 1 := by omega
      letI : Fact (1 < M + 1) := ⟨hmod⟩
      have hwrap : (x + 1).val = 0 := by
        rw [ZMod.val_add, ZMod.val_one, hxM]
        simp
      exact htail (ZMod.val_eq_zero (x + 1) |>.mp hwrap)
    have hmod : 1 < M + 1 := by omega
    letI : Fact (1 < M + 1) := ⟨hmod⟩
    rw [ZMod.val_add, ZMod.val_one,
      Nat.mod_eq_of_lt (by omega : x.val + 1 < M + 1)]
    omega
  · simp [ons_rectTailDartEquiv_apply, ons_rectDirStep, ons_rectDartValid,
      ons_rectDartBoundaryRank] at hd htail ⊢
    have hypos : 0 < y.val := by
      exact Nat.pos_of_ne_zero (fun h => hd (ZMod.val_eq_zero y |>.mp h))
    have hylt : y.val < N := by
      by_contra h
      have hyN : y.val = N := by
        have := ZMod.val_lt y
        omega
      have hmod : 1 < N + 1 := by omega
      letI : Fact (1 < N + 1) := ⟨hmod⟩
      have hwrap : (y + 1).val = 0 := by
        rw [ZMod.val_add, ZMod.val_one, hyN]
        simp
      exact htail (ZMod.val_eq_zero (y + 1) |>.mp hwrap)
    have hmod : 1 < N + 1 := by omega
    letI : Fact (1 < N + 1) := ⟨hmod⟩
    rw [ZMod.val_add, ZMod.val_one,
      Nat.mod_eq_of_lt (by omega : y.val + 1 < N + 1)]
    omega


end StatMech.Onsager
