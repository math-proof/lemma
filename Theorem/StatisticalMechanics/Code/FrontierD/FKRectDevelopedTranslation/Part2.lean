/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedTranslation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.FKRectColumnTranslation.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedWideCrossing
import Def.StatisticalMechanics.Code.FrontierD.FKRectDevelopedTranslation
open Set


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.RSW.Box

noncomputable section

@[simp] theorem fkRectDevelopedSiteTranslate_apply_zero
    (u : Int × Int) (z : Site 2) :
    fkRectDevelopedSiteTranslate u z 0 = z 0 + u.1 := by
  simp [fkRectDevelopedSiteTranslate]

@[simp] theorem fkRectDevelopedSiteTranslate_apply_one
    (u : Int × Int) (z : Site 2) :
    fkRectDevelopedSiteTranslate u z 1 = z 1 + u.2 := by
  simp [fkRectDevelopedSiteTranslate]


theorem fkRectSquareUndevelopPoint_add_checkerboardTranslation
    (z : Int × Int) (c t : Int) :
    fkRectSquareUndevelopPoint (z + (c + t, c - t)) =
      fkRectSquareUndevelopPoint z + (c, 2 * t) := by
  apply Prod.ext <;>
    simp [fkRectSquareUndevelopPoint] <;> omega

theorem fkRectIntModFin_add
    {N : Nat} (hN : 0 < N) (z s : Int) :
    fkRectIntModFin hN
        (((fkRectIntModFin hN z).val : Int) + s) =
      fkRectIntModFin hN (z + s) := by
  apply Fin.ext
  apply Nat.ModEq.eq_of_lt_of_lt
  · apply (ZMod.natCast_eq_natCast_iff _ _ N).mp
    rw [fkRectIntModFin_cast, fkRectIntModFin_cast]
    push_cast
    rw [fkRectIntModFin_cast]
  · exact (fkRectIntModFin hN
      (((fkRectIntModFin hN z).val : Int) + s)).isLt
  · exact (fkRectIntModFin hN (z + s)).isLt

theorem fkRectColumnTranslation_squareRepresentativeVertex
    (R : FKRectTorus) (c : Int) (z : Int × Int) :
    fkRectColumnTranslationVertexEquiv R c
        (fkRectSquareRepresentativeVertex R z) =
      fkRectSquareRepresentativeVertex R (z + (c, c)) := by
  apply Prod.ext
  · change fkRectColumnTranslate R c
        (fkRectIntModFin R.width_pos
          (z.2 + (z.1 - z.2) / 2)) =
      fkRectIntModFin R.width_pos
        (z.2 + c + (z.1 + c - (z.2 + c)) / 2)
    unfold fkRectColumnTranslate
    rw [fkRectIntModFin_add]
    congr 1
    ring
  · apply Fin.ext
    simp [fkRectColumnTranslationVertexEquiv_apply,
      fkRectSquareRepresentativeVertex,
      fkRectSquareUndevelopPoint]

theorem fkRectEvenRowTranslation_squareRepresentativeVertex
    (R : FKRectTorus) (t : Nat) : Even (2 * t) →
    ∀ z : Int × Int,
      fkRectEvenRowTranslationVertexEquiv R (2 * t)
          (fkRectSquareRepresentativeVertex R z) =
        fkRectSquareRepresentativeVertex R
          (z + ((t : Int), -(t : Int))) := by
  intro _ z
  apply Prod.ext
  · apply Fin.ext
    simp [fkRectEvenRowTranslationVertexEquiv_apply,
      fkRectSquareRepresentativeVertex,
      fkRectSquareUndevelopPoint]
    congr 1
    omega
  · change fkRectRowTranslate R (2 * t)
        (fkRectIntModFin R.height_pos (z.1 - z.2)) =
      fkRectIntModFin R.height_pos
        (z.1 + t - (z.2 + -(t : Int)))
    unfold fkRectRowTranslate
    rw [fkRectIntModFin_add]
    congr 1
    push_cast
    ring


end
end StatMech.FrontierD
