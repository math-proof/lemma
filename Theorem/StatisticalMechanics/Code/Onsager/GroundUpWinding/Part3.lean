/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GroundUpWinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Onsager.GroundUpWinding.Part2


namespace StatMech.Onsager.GroundUp

theorem RectPolygonData.umlaufsatz_aux (D : RectPolygonData) :
    ∀ n : ℕ, ∀ P : D.Poly, D.size P = n → D.simple P → D.balance P = 4 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro P hsz hsimple
    by_cases hr : D.rc P = 0
    · 
      have hcc : D.cc P = 4 := D.base P hsimple hr
      unfold RectPolygonData.balance
      omega
    · 
      have hrpos : 0 < D.rc P := lt_of_le_of_ne (D.hrc P) (Ne.symm hr)
      obtain ⟨P₁, P₂, hs₁, hs₂, hlt₁, hlt₂, hcceq, hrceq⟩ := D.chord P hsimple hrpos
      have hb₁ : D.balance P₁ = 4 := IH (D.size P₁) (hsz ▸ hlt₁) P₁ rfl hs₁
      have hb₂ : D.balance P₂ = 4 := IH (D.size P₂) (hsz ▸ hlt₂) P₂ rfl hs₂
      unfold RectPolygonData.balance at hb₁ hb₂ ⊢
      omega


theorem RectPolygonData.umlaufsatz (D : RectPolygonData) (P : D.Poly) (hP : D.simple P) :
    D.balance P = 4 :=
  D.umlaufsatz_aux (D.size P) P rfl hP


end StatMech.Onsager.GroundUp
