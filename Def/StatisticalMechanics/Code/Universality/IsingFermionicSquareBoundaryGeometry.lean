/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBoundaryGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion.Part19


namespace StatMech.Universality

open Complex

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareBoundaryTangent : FKIsingSquareBoundarySide → Complex
  | .bottom => 1
  | .right => Complex.I
  | .top => -1
  | .left => -Complex.I


def fkIsingSquareBoundaryPhase : FKIsingSquareBoundarySide → Complex
  | .bottom => 1
  | .right => isingLambda⁻¹
  | .top => Complex.I
  | .left => isingLambda


end
end StatMech.Universality
