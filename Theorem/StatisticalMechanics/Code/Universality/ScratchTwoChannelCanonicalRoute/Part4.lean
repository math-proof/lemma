/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part2
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

@[simp] theorem rlc_twoChannelPIMSSourceEdge_map {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (target : RlcTwoChannelPIMSVariableTargetEdge gamma gamma') :
    (rlc_twoChannelPIMSSourceEdge target).1.map Subtype.val =
      rlc_pimsEdgeEquiv (target.1.1.map Subtype.val) := by
  exact rlc_connectorCentralFaceEdgeLift_map _ target.2

theorem rlc_twoChannelPIMSSourceEdge_injective {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n} :
    Function.Injective
      (rlc_twoChannelPIMSSourceEdge (gamma := gamma) (gamma' := gamma')) := by
  intro target target' hsource
  apply Subtype.ext
  apply Subtype.ext
  apply Sym2.map.injective Subtype.val_injective
  apply rlc_pimsEdgeEquiv.injective
  rw [← rlc_twoChannelPIMSSourceEdge_map target,
    ← rlc_twoChannelPIMSSourceEdge_map target']
  exact congrArg (fun e :
    (rlc_connectorTwoChannelGraph gamma gamma').edgeSet =>
      e.1.map Subtype.val) hsource

theorem rlc_twoChannelPIMSSourceEdge_mem_central {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (target : RlcTwoChannelPIMSVariableTargetEdge gamma gamma') :
    (rlc_twoChannelPIMSSourceEdge target).1 ∈
      (rlc_connectorCentralFaceFiniteGraph gamma gamma').edgeSet := by
  let sourceSite := rlc_pimsEdgeEquiv (target.1.1.map Subtype.val)
  have hlat : sourceSite ∈ (hypercubicLattice 2).edgeSet :=
    rlc_pimsEdgeEquiv_mem_latticeEdge
      (rlc_twoChannelEdge_site_mem_lattice target.1)
  exact rlc_centralFaceEdgeLift_mem_graph sourceSite target.2 hlat


end
end StatMech.Universality
