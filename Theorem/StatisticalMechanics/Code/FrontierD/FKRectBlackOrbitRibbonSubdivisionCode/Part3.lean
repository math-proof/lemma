/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonSubdivisionCode.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonFlatGeometry
import Def.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonSubdivisionCode.Part3


namespace StatMech.FrontierD

open StatMech.Onsager

open StatMech.Onsager.BaseCase

noncomputable section

theorem fkRectRibbonSubdivisionCode_congr_direction
    (width height : ℕ) (hwidth : 0 < width) (hheight : 0 < height)
    (p : ZMod width × ZMod height) {mu nu : Fin 4}
    (h : mu = nu)
    (r : Fin (onsAnisotropicStepScale width height mu)) :
    fkRectRibbonSubdivisionCode width height hwidth hheight p mu r =
      fkRectRibbonSubdivisionCode width height hwidth hheight p nu
        (fkRectRibbonSubdivisionResidueCongr width height h r) := by
  subst nu
  rfl

theorem fkRectRibbonSubdivisionCode_fixed_injective
    (width height : ℕ) (hwidth : 0 < width) (hheight : 0 < height)
    (p : ZMod width × ZMod height) (mu : Fin 4) :
    Function.Injective
      (fkRectRibbonSubdivisionCode width height hwidth hheight p mu) := by
  letI : NeZero width := ⟨hwidth.ne'⟩
  letI : NeZero height := ⟨hheight.ne'⟩
  fin_cases mu
  · intro r s h
    have hrs := congrArg
      (fun c : (Fin width × Fin height) × (Fin height × Fin width) => c.1.2) h
    simpa [fkRectRibbonSubdivisionCode] using hrs
  · intro r s h
    have hrs := congrArg
      (fun c : (Fin width × Fin height) × (Fin height × Fin width) => c.2.2) h
    simpa [fkRectRibbonSubdivisionCode] using hrs
  · intro r s h
    have hrs := congrArg
      (fun c : (Fin width × Fin height) × (Fin height × Fin width) => c.1) h
    have hpairs :
        ((⟨p.1.val, p.1.val_lt⟩ : Fin width), r) =
          ((⟨p.1.val, p.1.val_lt⟩ : Fin width), s) := by
      apply fkRectRibbonBackwardCode_injective hwidth hheight
      simpa [fkRectRibbonSubdivisionCode] using hrs
    exact congrArg Prod.snd hpairs
  · intro r s h
    have hrs := congrArg
      (fun c : (Fin width × Fin height) × (Fin height × Fin width) => c.2) h
    have hpairs :
        ((⟨p.2.val, p.2.val_lt⟩ : Fin height), r) =
          ((⟨p.2.val, p.2.val_lt⟩ : Fin height), s) := by
      apply fkRectRibbonBackwardCode_injective hheight hwidth
      simpa [fkRectRibbonSubdivisionCode] using hrs
    exact congrArg Prod.snd hpairs

end
end StatMech.FrontierD
