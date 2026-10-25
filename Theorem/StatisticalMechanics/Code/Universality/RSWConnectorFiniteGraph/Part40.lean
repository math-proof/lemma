/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWGapSymmetry.Part4
import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalTraceContact
import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalSelectionObstruction
import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part6
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.OffCentreDomination.Part13
import Theorem.StatisticalMechanics.Code.FK.WeightedParameterMonotoneClosed
import Theorem.StatisticalMechanics.Code.FrontierD.FKBoundarySingleMerge
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Def.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part58
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorVariableEdge_preimage_mem_connector {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (e : (rlc_connectorPIMSVariableGraph gamma gamma').edgeSet) :
    rlc_pimsEdgeEquiv (e.1.map Subtype.val) ∈
      rlc_connectorEdges gamma gamma' := by
  induction heq : e.1 using Sym2.inductionOn with
  | _ x y =>
      have he := e.2
      rw [heq, SimpleGraph.mem_edgeSet] at he
      simpa [heq, Sym2.map_mk] using he.2

theorem rlc_connectorVariableEdge_map_mem_lattice {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (e : (rlc_connectorPIMSVariableGraph gamma gamma').edgeSet) :
    e.1.map Subtype.val ∈ (hypercubicLattice 2).edgeSet := by
  induction heq : e.1 using Sym2.inductionOn with
  | _ x y =>
      have he := e.2
      rw [heq, SimpleGraph.mem_edgeSet] at he
      rw [Sym2.map_mk, SimpleGraph.mem_edgeSet]
      exact he.1.1


end
end StatMech.Universality
