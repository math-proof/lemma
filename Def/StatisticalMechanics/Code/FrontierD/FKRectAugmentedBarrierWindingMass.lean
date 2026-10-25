/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectAugmentedBarrierWindingMass.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectAugmentedSourceBarrier.Part2
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def fkRectIndexedConfigurationOfFullGraph (R : FKRectTorus)
    (rho : ConfigSpace (Sym2 R.Vertex)) : R.Configuration :=
  (fkRectFullEdgeConfigEquiv R).symm
    (FK.ecz_closeOff (fkRectTorusGraph R) rho)

end
end StatMech.FrontierD
