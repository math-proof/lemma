/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part40
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_twoChannelFullMaxComponentTraceRep_onEither {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (C : RlcTwoChannelFullMaxOutsideComponent gamma gamma') :
    rlc_connectorOnEither gamma gamma'
      (rlc_twoChannelFullMaxComponentTraceRep gamma gamma' C) := by
  classical
  unfold rlc_twoChannelFullMaxComponentTraceRep
  split
  · exact Or.inl (rlc_connectorRightAnchor_onRight gamma)
  · exact Or.inr (rlc_connectorLeftAnchor_onLeft gamma')

theorem rlc_twoChannelFullMaxComponentTraceRep_eq_or_mergedClique_adj
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (C D : RlcTwoChannelFullMaxOutsideComponent gamma gamma') :
    rlc_twoChannelFullMaxComponentTraceRep gamma gamma' C =
        rlc_twoChannelFullMaxComponentTraceRep gamma gamma' D ∨
      (rlc_connectorMergedClique gamma gamma').Adj
        (rlc_twoChannelFullMaxComponentTraceRep gamma gamma' C)
        (rlc_twoChannelFullMaxComponentTraceRep gamma gamma' D) := by
  by_cases hCD : rlc_twoChannelFullMaxComponentTraceRep gamma gamma' C =
      rlc_twoChannelFullMaxComponentTraceRep gamma gamma' D
  · exact Or.inl hCD
  · right
    rw [rlc_connectorMergedClique,
      Lattice.boundaryCliqueGraph_adj]
    exact ⟨hCD,
      rlc_twoChannelFullMaxComponentTraceRep_onEither gamma gamma' C,
      rlc_twoChannelFullMaxComponentTraceRep_onEither gamma gamma' D⟩


theorem rlc_twoChannelFullMaxWiring_traceRep_eq_or_mergedClique_adj
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {x y : RlcTwoChannelFullInnerVertex gamma gamma'}
    (hxy : (rlc_twoChannelFullInnerMaxSupportedWiring gamma gamma').Adj x y) :
    rlc_twoChannelFullMaxComponentTraceRep gamma gamma'
          (rlc_twoChannelFullMaxInnerContraction gamma gamma' x) =
        rlc_twoChannelFullMaxComponentTraceRep gamma gamma'
          (rlc_twoChannelFullMaxInnerContraction gamma gamma' y) ∨
      (rlc_connectorMergedClique gamma gamma').Adj
        (rlc_twoChannelFullMaxComponentTraceRep gamma gamma'
          (rlc_twoChannelFullMaxInnerContraction gamma gamma' x))
        (rlc_twoChannelFullMaxComponentTraceRep gamma gamma'
          (rlc_twoChannelFullMaxInnerContraction gamma gamma' y)) := by
  exact Or.inl (congrArg
    (rlc_twoChannelFullMaxComponentTraceRep gamma gamma')
    (rlc_twoChannelFullMaxInnerContraction_eq_of_maxWiring
      gamma gamma' hxy))

end
end StatMech.Universality
