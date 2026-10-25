/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part10
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

noncomputable def rlc_twoChannelFullVariableGraph {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    SimpleGraph (RlcConnectorVertex n) where
  Adj x y := (rlc_connectorTwoChannelGraph gamma gamma').Adj x y ∧
    Nonempty (RlcTwoChannelAmbientSourceEdge gamma gamma'
      (rlc_pimsEdgeEquiv (s(x, y).map Subtype.val)))
  symm := by
    constructor
    rintro x y ⟨hxy, hsource⟩
    refine ⟨hxy.symm, ?_⟩
    simpa [Sym2.eq_swap] using hsource
  loopless := ⟨fun x hxx => hxx.1.ne rfl⟩

end
end StatMech.Universality
