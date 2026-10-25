/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Instance.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part2
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

noncomputable def rlc_twoChannelFullExteriorGraph {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    SimpleGraph (RlcConnectorVertex n) where
  Adj x y := (rlc_connectorTwoChannelGraph gamma gamma').Adj x y ∧
    ¬Nonempty (RlcTwoChannelAmbientSourceEdge gamma gamma'
      (rlc_pimsEdgeEquiv (s(x, y).map Subtype.val))) ∧
    rlc_pimsEdgeEquiv (s(x, y).map Subtype.val) ∉
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1
  symm := by
    constructor
    rintro x y ⟨hxy, hsource, htrace⟩
    refine ⟨hxy.symm, ?_, ?_⟩
    · simpa [Sym2.eq_swap] using hsource
    · simpa [Sym2.eq_swap] using htrace
  loopless := ⟨fun x hxx => hxx.1.ne rfl⟩

end
end StatMech.Universality
