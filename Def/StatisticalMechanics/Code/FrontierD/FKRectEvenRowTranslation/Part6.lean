/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEvenRowTranslation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedAxisSource
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEvenRowTranslation.Part5
open Set SimpleGraph StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

def fkRectOpenGraphEvenRowTranslationIso
    (R : FKRectTorus) (s : Nat) (hs : Even s)
    (omega : R.Configuration) :
    fkRectOpenGraph R omega ≃g
      fkRectOpenGraph R
        (fkRectEvenRowTranslationConfigurationEquiv R s omega) where
  toEquiv := fkRectEvenRowTranslationVertexEquiv R s
  map_rel_iff' := by
    intro x y
    exact fkRectOpenGraph_evenRowTranslation_adj R s hs omega x y

end
end StatMech.FrontierD
