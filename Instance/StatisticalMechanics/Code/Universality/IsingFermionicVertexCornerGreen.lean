/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCappedTent
import Abbrev.StatisticalMechanics.Code.Universality.IsingFermionicVertexCornerGreen


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

noncomputable local instance fkIsingSquareAvailableDirectionFintype
    (n : Nat) (x : FKIsingSquareFullVertexNode n) :
    Fintype (FKIsingSquareAvailableDirection n x) :=
  Fintype.ofFinite _


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
