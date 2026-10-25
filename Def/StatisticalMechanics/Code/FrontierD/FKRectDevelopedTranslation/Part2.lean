/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedTranslation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.FKRectColumnTranslation.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedWideCrossing
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedTranslation.Part2
open Set


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.RSW.Box

noncomputable section

def fkRectCheckerboardTranslationVertexEquiv
    (R : FKRectTorus) (c : Int) (t : Nat) : R.Vertex ≃ R.Vertex :=
  (fkRectEvenRowTranslationVertexEquiv R (2 * t)).trans
    (fkRectColumnTranslationVertexEquiv R c)

def fkRectCheckerboardTranslationConfigurationEquiv
    (R : FKRectTorus) (c : Int) (t : Nat) :
    R.Configuration ≃ R.Configuration :=
  (fkRectEvenRowTranslationConfigurationEquiv R (2 * t)).trans
    (fkRectColumnTranslationConfigurationEquiv R c)

end
end StatMech.FrontierD
