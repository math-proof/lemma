/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderCrossings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderLaw.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderCrossings.Part2
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectHorizontalCylinderCrossingRepresentativeIndices
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex)) :
    Finset (Fin R.width) := by
  classical
  exact Finset.univ.image
    (fkRectHorizontalCylinderCrossingRepresentative R rho)

end
end StatMech.FrontierD
