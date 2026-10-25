/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEvenRowTranslation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedAxisSource
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEvenRowTranslation.Part3
open Set SimpleGraph StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

def fkRectEvenRowTranslationEdgeEquiv
    (R : FKRectTorus) (s : Nat) : R.EdgeIndex ≃ R.EdgeIndex :=
  (Equiv.refl Bool).prodCongr
    ((Equiv.refl (Fin R.width)).prodCongr
      (fkRectRowTranslationEquiv R s))

end
end StatMech.FrontierD
