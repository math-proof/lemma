/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFaceCornerGreen.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCappedTent
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFaceCornerGreen


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

def faceTopRowCap
    (n : Nat) (source c : FKIsingSquareFullFaceNode n) : Real :=
  isingNatReverseCappedTent (2 * n - 1) source.2.1 c.2.1

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
