/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquareReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedWideCrossing
import Theorem.StatisticalMechanics.Code.FK.TranslationInvariance.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquareReflection
open Set SimpleGraph StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

def fkRectRowReflectionEquiv (R : FKRectTorus) (center : Nat) :
    Fin R.height ≃ Fin R.height where
  toFun := fkRectRowReflection R center
  invFun := fkRectRowReflection R center
  left_inv := fkRectRowReflection_involutive R center
  right_inv := fkRectRowReflection_involutive R center

end
end StatMech.FrontierD
