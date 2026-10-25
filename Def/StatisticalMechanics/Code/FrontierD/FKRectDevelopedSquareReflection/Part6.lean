/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquareReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedWideCrossing
import Theorem.StatisticalMechanics.Code.FK.TranslationInvariance.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquareReflection.Part5
open Set SimpleGraph StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

def fkRectOpenGraphDevelopedReflectionIso
    (R : FKRectTorus) (center : Nat) (omega : R.Configuration) :
    fkRectOpenGraph R omega ≃g
      fkRectOpenGraph R
        (fkRectDevelopedReflectionConfigurationEquiv R center omega) where
  toEquiv := fkRectDevelopedReflectionVertexEquiv R center
  map_rel_iff' := by
    intro x y
    exact fkRectOpenGraph_developedReflection_adj R center omega x y


end
end StatMech.FrontierD
