/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSeamForcing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectNoLoopNormalization
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSeamForcing.Part4
open Finset


namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectCriticalCutHorizontalCrossingSourceMass
    (R : FKRectTorus) (q : Real) (y : Fin R.height) : Real := by
  classical
  exact ∑ omega : R.Configuration,
    if FKRectCutHorizontalCrossingSource R omega y then
      fkRectCriticalRandomClusterProb R q omega
    else 0


def fkRectCriticalCutHorizontalCrossingSourceExpectation
    (R : FKRectTorus) (q : Real) : Real :=
  ∑ omega : R.Configuration,
    fkRectCriticalRandomClusterProb R q omega *
      fkRectCutHorizontalCrossingSourceCount R omega


def fkRectCriticalCutHorizontalCrossingClusterExpectation
    (R : FKRectTorus) (q : Real) : Real :=
  ∑ omega : R.Configuration,
    fkRectCriticalRandomClusterProb R q omega *
      fkRectCutHorizontalCrossingClusterCount R omega

end
end StatMech.FrontierD
