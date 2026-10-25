/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Abbrev.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part3
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_twoChannelFullSourceEdge_exists {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (target : RlcTwoChannelFullVariableTargetEdge gamma gamma') :
    ∃ source : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet,
      source.1.map Subtype.val =
        rlc_pimsEdgeEquiv (target.1.map Subtype.val) := by
  classical
  induction ht : target.1 using Sym2.inductionOn with
  | _ x y =>
      have hadj := target.2
      rw [ht, SimpleGraph.mem_edgeSet] at hadj
      have hsource : Nonempty (RlcTwoChannelAmbientSourceEdge gamma gamma'
          (rlc_pimsEdgeEquiv (s(x, y).map Subtype.val))) := hadj.2
      obtain ⟨source⟩ := hsource
      exact ⟨source.1, by simpa [ht] using source.2⟩


end
end StatMech.Universality
