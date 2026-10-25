/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectColumnTranslation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectOrientedEvenRowBlock.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectColumnTranslation.Part5
open Set SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def fkRectOpenGraphColumnTranslationIso
    (R : FKRectTorus) (s : Int) (omega : R.Configuration) :
    fkRectOpenGraph R omega ≃g
      fkRectOpenGraph R
        (fkRectColumnTranslationConfigurationEquiv R s omega) where
  toEquiv := fkRectColumnTranslationVertexEquiv R s
  map_rel_iff' := by
    intro x y
    exact fkRectOpenGraph_columnTranslation_adj R s omega x y

end
end StatMech.FrontierD
