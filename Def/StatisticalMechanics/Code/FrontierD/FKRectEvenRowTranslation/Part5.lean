/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEvenRowTranslation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedAxisSource
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEvenRowTranslation.Part4
open Set SimpleGraph StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

def fkRectEvenRowTranslationConfigurationEquiv
    (R : FKRectTorus) (s : Nat) : R.Configuration ≃ R.Configuration :=
  Equiv.arrowCongr (fkRectEvenRowTranslationEdgeEquiv R s)
    (Equiv.refl Bool)

end
end StatMech.FrontierD
