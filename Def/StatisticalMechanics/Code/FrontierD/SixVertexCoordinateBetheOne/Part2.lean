/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCoordinateBetheOne.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCoordinateBethe.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCoordinateBetheOne
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

def sixVertexOneSectorEquiv (N : ℕ) : SixVertexSector N 1 ≃ Fin N where
  toFun x := sixVertexSectorPosition x 0
  invFun := sixVertexSingletonSector
  left_inv := fun x => (sixVertexSector_eq_singleton_position x).symm
  right_inv := sixVertexSectorPosition_singleton

end
end StatMech.FrontierD
