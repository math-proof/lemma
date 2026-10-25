/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Instance.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part3
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_openSub_twoChannelFullDual_eq_variable_sup_exterior {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    FK.openSub (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_twoChannelFullDualConfig gamma gamma' omega) =
      FK.openSub (rlc_twoChannelFullVariableGraph gamma gamma')
          (rlc_twoChannelFullDualConfig gamma gamma' omega) ⊔
        rlc_twoChannelFullExteriorGraph gamma gamma' := by
  classical
  ext x y
  simp only [FK.openSub_adj, SimpleGraph.sup_adj]
  let e : Sym2 (RlcConnectorVertex n) := s(x, y)
  let source := RlcTwoChannelAmbientSourceEdge gamma gamma'
    (rlc_pimsEdgeEquiv (e.map Subtype.val))
  constructor
  · rintro ⟨htarget, hopen⟩
    by_cases hsource : Nonempty source
    · have hs : Nonempty (RlcTwoChannelAmbientSourceEdge gamma gamma'
          (rlc_pimsEdgeEquiv (s(x, y).map Subtype.val))) := by
          simpa only [source, e] using hsource
      exact Or.inl ⟨⟨htarget, hs⟩, hopen⟩
    · by_cases htrace : rlc_pimsEdgeEquiv (e.map Subtype.val) ∈
          rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1
      · have hclosed := rlc_twoChannelFullDualConfig_of_no_source
          gamma gamma' omega e (by simpa [source] using hsource)
        rw [if_pos htrace] at hclosed
        exact False.elim (by simpa [e, hclosed] using hopen)
      · exact Or.inr ⟨htarget, by simpa [source, e] using hsource,
          by simpa [e] using htrace⟩
  · rintro (hvariable | hexterior)
    · exact ⟨hvariable.1.1, hvariable.2⟩
    · refine ⟨hexterior.1, ?_⟩
      have hopen := rlc_twoChannelFullDualConfig_of_no_source
        gamma gamma' omega e (by simpa [source, e] using hexterior.2.1)
      rw [if_neg hexterior.2.2] at hopen
      simpa [e] using hopen

end
end StatMech.Universality
