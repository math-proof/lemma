/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Instance.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part6
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

@[simp] theorem rlc_twoChannelIndexedFaceProjection_face {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (C : Ising.kwg_Face
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')) :
    rlc_twoChannelIndexedFaceProjection gamma gamma'
        (rlc_twoChannelIndexedOuterFace gamma gamma' C) = C :=
  rfl


theorem rlc_twoChannelIndexedSpoke_adj_face {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (x : RlcTwoChannelIndexedOuterVertex gamma gamma')
    (hx : ¬RlcTwoChannelIndexedIsFace gamma gamma' x) :
    (rlc_twoChannelIndexedSpokeGraph gamma gamma').Adj x
      (rlc_twoChannelIndexedOuterFace gamma gamma'
        (rlc_twoChannelIndexedFaceProjection gamma gamma' x)) := by
  refine ⟨?_, rfl, Or.inr trivial⟩
  intro h
  rw [h] at hx
  exact hx trivial


theorem rlc_twoChannelIndexedFaceProjection_eq_of_spoke {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {x y : RlcTwoChannelIndexedOuterVertex gamma gamma'}
    (hxy : (rlc_twoChannelIndexedSpokeGraph gamma gamma').Adj x y) :
    rlc_twoChannelIndexedFaceProjection gamma gamma' x =
      rlc_twoChannelIndexedFaceProjection gamma gamma' y :=
  hxy.2.1

end
end StatMech.Universality
