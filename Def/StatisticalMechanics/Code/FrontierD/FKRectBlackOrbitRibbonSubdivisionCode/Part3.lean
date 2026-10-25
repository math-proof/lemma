/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonSubdivisionCode.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonFlatGeometry
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonSubdivisionCode.Part2


namespace StatMech.FrontierD

open StatMech.Onsager

open StatMech.Onsager.BaseCase

noncomputable section

def fkRectRibbonSubdivisionCode
    (width height : ℕ) (hwidth : 0 < width) (hheight : 0 < height)
    (p : ZMod width × ZMod height) (mu : Fin 4)
    (r : Fin (onsAnisotropicStepScale width height mu)) :
    (Fin width × Fin height) × (Fin height × Fin width) := by
  letI : NeZero width := ⟨hwidth.ne'⟩
  letI : NeZero height := ⟨hheight.ne'⟩
  let px : Fin width := ⟨p.1.val, p.1.val_lt⟩
  let py : Fin height := ⟨p.2.val, p.2.val_lt⟩
  exact match mu with
  | 0 => ((px, r), (py, 0))
  | 1 => ((px, 0), (py, r))
  | 2 => (fkRectRibbonBackwardCode hwidth hheight px r, (py, 0))
  | 3 => ((px, 0), fkRectRibbonBackwardCode hheight hwidth py r)


def fkRectRibbonSubdivisionResidueCongr
    (width height : ℕ) {mu nu : Fin 4} (h : mu = nu) :
    Fin (onsAnisotropicStepScale width height mu) ≃
      Fin (onsAnisotropicStepScale width height nu) :=
  finCongr (congrArg (onsAnisotropicStepScale width height) h)

end
end StatMech.FrontierD
