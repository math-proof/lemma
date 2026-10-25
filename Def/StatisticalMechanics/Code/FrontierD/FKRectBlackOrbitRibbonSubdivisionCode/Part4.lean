/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonSubdivisionCode.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonFlatGeometry
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonSubdivisionCode.Part3


namespace StatMech.FrontierD

open StatMech.Onsager

open StatMech.Onsager.BaseCase

noncomputable section

def fkRectRibbonSubdivisionCodeEmbed
    (width height : ℕ)
    (c : (Fin width × Fin height) × (Fin height × Fin width)) :
    ZMod (width * height) × ZMod (width * height) :=
  ((finProdFinEquiv c.1).val, (finProdFinEquiv c.2).val)

end
end StatMech.FrontierD
