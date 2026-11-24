module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedWideCrossing
public import Theorem.StatisticalMechanics.Code.FK.TranslationInvariance.Part5
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquareReflection.Part4
open Set SimpleGraph StatMech.Lattice


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquareReflection.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def fkRectDevelopedReflectionConfigurationEquiv
    (R : FKRectTorus) (center : Nat) :
    R.Configuration ≃ R.Configuration :=
  Equiv.arrowCongr (fkRectDevelopedReflectionEdgeEquiv R center)
    (Equiv.refl Bool)

end
end StatMech.FrontierD
