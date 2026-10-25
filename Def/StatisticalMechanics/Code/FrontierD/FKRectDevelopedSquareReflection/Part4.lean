/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquareReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedWideCrossing
import Theorem.StatisticalMechanics.Code.FK.TranslationInvariance.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquareReflection.Part3
open Set SimpleGraph StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

def fkRectDevelopedReflectionEdgeEquiv (R : FKRectTorus) (center : Nat) :
    R.EdgeIndex ≃ R.EdgeIndex :=
  (Equiv.refl Bool).prodCongr
    ((Equiv.refl (Fin R.width)).prodCongr
      ((fkRectRowReflectionEquiv R center).trans
        (svFinitePeriodicSuccEquiv R.height_pos)))

end
end StatMech.FrontierD
