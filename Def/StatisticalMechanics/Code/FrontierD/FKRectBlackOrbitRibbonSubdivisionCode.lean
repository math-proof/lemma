/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonSubdivisionCode.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonFlatGeometry


namespace StatMech.FrontierD

open StatMech.Onsager

open StatMech.Onsager.BaseCase

noncomputable section

def fkRectRibbonBackwardCode {M S : ℕ} (hM : 0 < M) (hS : 0 < S)
    (p : Fin M) (r : Fin S) : Fin M × Fin S := by
  letI : NeZero S := ⟨hS.ne'⟩
  exact
  if hr : r.val = 0 then (p, 0)
  else
    (SixVertexArrows.cyclicPred hM p,
      ⟨S - r.val, by omega⟩)

end
end StatMech.FrontierD
