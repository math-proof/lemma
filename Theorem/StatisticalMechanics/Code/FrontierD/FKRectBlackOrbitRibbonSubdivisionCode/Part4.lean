/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonSubdivisionCode.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonFlatGeometry
import Def.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonSubdivisionCode.Part4


namespace StatMech.FrontierD

open StatMech.Onsager

open StatMech.Onsager.BaseCase

noncomputable section

theorem fkRectRibbonSubdivisionCodeEmbed_injective
    (width height : ℕ) [NeZero width] [NeZero height] :
    Function.Injective (fkRectRibbonSubdivisionCodeEmbed width height) := by
  intro c e h
  have hx := congrArg (fun z : ZMod (width * height) ×
      ZMod (width * height) => z.1.val) h
  have hy := congrArg (fun z : ZMod (width * height) ×
      ZMod (width * height) => z.2.val) h
  simp only [fkRectRibbonSubdivisionCodeEmbed, ZMod.val_natCast] at hx hy
  have hcx : (finProdFinEquiv c.1).val < width * height :=
    (finProdFinEquiv c.1).isLt
  have hex : (finProdFinEquiv e.1).val < width * height :=
    (finProdFinEquiv e.1).isLt
  have hcy : (finProdFinEquiv c.2).val < width * height :=
    by simpa [Nat.mul_comm] using (finProdFinEquiv c.2).isLt
  have hey : (finProdFinEquiv e.2).val < width * height :=
    by simpa [Nat.mul_comm] using (finProdFinEquiv e.2).isLt
  rw [Nat.mod_eq_of_lt hcx, Nat.mod_eq_of_lt hex] at hx
  rw [Nat.mod_eq_of_lt hcy, Nat.mod_eq_of_lt hey] at hy
  exact Prod.ext (finProdFinEquiv.injective (Fin.ext hx))
    (finProdFinEquiv.injective (Fin.ext hy))

end
end StatMech.FrontierD
