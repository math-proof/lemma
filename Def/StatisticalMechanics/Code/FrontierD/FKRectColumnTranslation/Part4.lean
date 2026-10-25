/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectColumnTranslation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectOrientedEvenRowBlock.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectColumnTranslation.Part3
open Set SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def fkRectColumnTranslationEdgeEquiv
    (R : FKRectTorus) (s : Int) : R.EdgeIndex ≃ R.EdgeIndex :=
  (Equiv.refl Bool).prodCongr
    ((fkRectColumnTranslationEquiv R s).prodCongr
      (Equiv.refl (Fin R.height)))

end
end StatMech.FrontierD
