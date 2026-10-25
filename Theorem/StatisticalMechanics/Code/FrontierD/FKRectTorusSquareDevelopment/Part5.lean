/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDevelopedWinding.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetFull.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareDevelopment.Part5


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem mem_fkRectSquareDeckLattice_iff
    (R : FKRectTorus) (z : Int × Int) :
    z ∈ fkRectSquareDeckLattice R ↔
      ∃ u : Int × Int, fkRectSquareDeckTranslation R u = z :=
  by
    change z ∈ (fkRectSquareDeckHom R).range ↔ _
    simpa [fkRectSquareDeckHom] using
      (AddMonoidHom.mem_range (f := fkRectSquareDeckHom R) (y := z))


theorem fkRectSquareDevelopPoint_add_period
    (R : FKRectTorus) (p u : Int × Int) :
    fkRectSquareDevelopPoint
          (p.1 + (R.width : Int) * u.1,
            p.2 + (R.height : Int) * u.2) -
        fkRectSquareDevelopPoint p =
      fkRectSquareDeckTranslation R u := by
  have hhNat : 2 * (R.height / 2) = R.height :=
    Nat.two_mul_div_two_of_even R.height_even
  have hh : (2 : Int) * (R.height / 2 : Nat) = R.height := by
    exact_mod_cast hhNat
  have hhalf : ((R.height : Int) * u.2) / 2 =
      (R.height / 2 : Nat) * u.2 := by
    rw [← hh]
    rw [show (2 : Int) * (R.height / 2 : Nat) * u.2 =
      2 * ((R.height / 2 : Nat) * u.2) by ring]
    exact Int.mul_ediv_cancel_left _ (by norm_num)
  have hdiv : (2 : Int) ∣ (R.height : Int) * u.2 := by
    refine ⟨(R.height / 2 : Nat) * u.2, ?_⟩
    rw [← hh]
    ring
  have hceil :
      (p.2 + (R.height : Int) * u.2 + 1) / 2 =
        (p.2 + 1) / 2 + (R.height / 2 : Nat) * u.2 := by
    rw [show p.2 + (R.height : Int) * u.2 + 1 =
      (p.2 + 1) + (R.height : Int) * u.2 by ring]
    rw [Int.add_ediv_of_dvd_right hdiv, hhalf]
  have hfloor :
      (p.2 + (R.height : Int) * u.2) / 2 =
        p.2 / 2 + (R.height / 2 : Nat) * u.2 := by
    rw [Int.add_ediv_of_dvd_right hdiv, hhalf]
  apply Prod.ext <;>
    simp [fkRectSquareDevelopPoint, fkRectSquareDeckTranslation,
      hceil, hfloor] <;>
    ring


theorem fkRectSquareUndevelopPoint_add_deck
    (R : FKRectTorus) (p u : Int × Int) :
    fkRectSquareUndevelopPoint (p + fkRectSquareDeckTranslation R u) =
      ((fkRectSquareUndevelopPoint p).1 + (R.width : Int) * u.1,
        (fkRectSquareUndevelopPoint p).2 + (R.height : Int) * u.2) := by
  apply fkRectSquareDevelopPoint_injective
  rw [fkRectSquareDevelopPoint_undevelopPoint]
  have h := fkRectSquareDevelopPoint_add_period R
    (fkRectSquareUndevelopPoint p) u
  rw [fkRectSquareDevelopPoint_undevelopPoint] at h
  apply Prod.ext
  · have h' := congrArg Prod.fst h
    simp only [Prod.fst_sub, Prod.fst_add] at h' ⊢
    omega
  · have h' := congrArg Prod.snd h
    simp only [Prod.snd_sub, Prod.snd_add] at h' ⊢
    omega


end
end StatMech.FrontierD
