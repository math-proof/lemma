/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part18
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

def RlcTwoChannelIndexedIsFace {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    RlcTwoChannelIndexedOuterVertex gamma gamma' → Prop
  | Sum.inr (Sum.inr _) => True
  | _ => False

noncomputable def rlc_twoChannelIndexedSpokeGraph {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    SimpleGraph (RlcTwoChannelIndexedOuterVertex gamma gamma') where
  Adj x y := x ≠ y ∧
    rlc_twoChannelIndexedFaceProjection gamma gamma' x =
      rlc_twoChannelIndexedFaceProjection gamma gamma' y ∧
    (RlcTwoChannelIndexedIsFace gamma gamma' x ∨
      RlcTwoChannelIndexedIsFace gamma gamma' y)
  symm := by
    constructor
    rintro x y ⟨hne, hface, hghost⟩
    exact ⟨hne.symm, hface.symm, hghost.symm⟩
  loopless := ⟨fun x h => h.1 rfl⟩

end
end StatMech.Universality
