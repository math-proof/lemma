/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectColumnTranslation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectOrientedEvenRowBlock.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKRectColumnTranslation.Part3
open Set SimpleGraph


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkRectColumnTranslationVertexEquiv_apply
    (R : FKRectTorus) (s : Int) (v : R.Vertex) :
    fkRectColumnTranslationVertexEquiv R s v =
      (fkRectColumnTranslate R s v.1, v.2) := rfl


end
end StatMech.FrontierD
