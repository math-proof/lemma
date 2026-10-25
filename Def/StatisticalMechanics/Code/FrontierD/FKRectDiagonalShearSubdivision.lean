/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDiagonalShearSubdivision.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareDevelopment.Part12
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
open SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Universality

noncomputable section

def fkRectDiagonalShearPoint (p : Int × Int) : Site 2 :=
  ![p.1 + p.2, p.1 - p.2]


def fkRectDiagonalShearMidpoint (p q : Int × Int) : Site 2 :=
  ![(fkRectDiagonalShearPoint q) 0, (fkRectDiagonalShearPoint p) 1]

end
end StatMech.FrontierD
