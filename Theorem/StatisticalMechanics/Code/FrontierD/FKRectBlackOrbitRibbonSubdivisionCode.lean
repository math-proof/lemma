/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonSubdivisionCode.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonFlatGeometry
import Def.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonSubdivisionCode


namespace StatMech.FrontierD

open StatMech.Onsager

open StatMech.Onsager.BaseCase

noncomputable section

theorem fkRectRibbonBackwardCode_injective
    {M S : ℕ} (hM : 0 < M) (hS : 0 < S) :
    Function.Injective (fun z : Fin M × Fin S =>
      fkRectRibbonBackwardCode hM hS z.1 z.2) := by
  rintro ⟨p, r⟩ ⟨q, s⟩ h
  by_cases hr : r.val = 0 <;> by_cases hs : s.val = 0
  · simp [fkRectRibbonBackwardCode, hr, hs] at h
    exact Prod.ext h (Fin.ext (hr.trans hs.symm))
  · have hres := congrArg (fun z : Fin M × Fin S => z.2.val) h
    simp [fkRectRibbonBackwardCode, hr, hs] at hres
    change 0 = S - s.val at hres
    omega
  · have hres := congrArg (fun z : Fin M × Fin S => z.2.val) h
    simp [fkRectRibbonBackwardCode, hr, hs] at hres
    change S - r.val = 0 at hres
    omega
  · have hcell := congrArg (fun z : Fin M × Fin S => z.1) h
    have hres := congrArg (fun z : Fin M × Fin S => z.2.val) h
    simp [fkRectRibbonBackwardCode, hr, hs] at hcell hres
    have hpq : p = q := by
      rw [← finitePeriodicSucc_cyclicPred hM p,
        ← finitePeriodicSucc_cyclicPred hM q, hcell]
    change S - r.val = S - s.val at hres
    have hrle : r.val ≤ S := by omega
    have hsle : s.val ≤ S := by omega
    have hcast := congrArg (fun z : Nat => (z : Int)) hres
    change ((S - r.val : Nat) : Int) = ((S - s.val : Nat) : Int) at hcast
    rw [Nat.cast_sub hrle, Nat.cast_sub hsle] at hcast
    have hrs : r = s := Fin.ext (by omega)
    exact Prod.ext hpq hrs

theorem fkRectRibbon_forward_eq_backward
    {M S : ℕ} (hM : 0 < M) (hS : 0 < S)
    (p q : Fin M) (r s : Fin S)
    (h : (p, r) = fkRectRibbonBackwardCode hM hS q s) :
    (r.val = 0 ∧ s.val = 0 ∧ p = q) ∨
      (r.val ≠ 0 ∧ s.val ≠ 0 ∧
        p = SixVertexArrows.cyclicPred hM q ∧ r.val + s.val = S) := by
  by_cases hs : s.val = 0
  · left
    simp [fkRectRibbonBackwardCode, hs] at h
    exact ⟨congrArg Fin.val h.2, hs, h.1⟩
  · right
    have hcell := congrArg (fun z : Fin M × Fin S => z.1) h
    have hres := congrArg (fun z : Fin M × Fin S => z.2.val) h
    simp [fkRectRibbonBackwardCode, hs] at hcell hres
    have hsum : r.val + s.val = S := by
      change r.val = S - s.val at hres
      omega
    exact ⟨fun hr => by omega, hs, hcell, hsum⟩

end
end StatMech.FrontierD
