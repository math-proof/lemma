module
public import Theorem.StatisticalMechanics.Code.Universality.RSWGapSymmetry.Part4
public import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalTraceContact
public import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalSelectionObstruction
public import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part6
public import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
public import Theorem.StatisticalMechanics.Code.FK.OffCentreDomination.Part13
public import Theorem.StatisticalMechanics.Code.FK.WeightedParameterMonotoneClosed
public import Theorem.StatisticalMechanics.Code.FrontierD.FKBoundarySingleMerge
public import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
public import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part28
open Finset SimpleGraph Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def rlc_connectorAugmentedEdgeToCollared {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Ising.kwg_Edge (rlc_connectorAugmentedPlanarDomain gamma gamma') →
      Ising.kwg_Edge (rlc_connectorCollaredPlanarDomain gamma gamma') :=
  fun e => ⟨e.1.map (rlc_connectorVertexToCollared gamma gamma'), by
    have he := e.2
    induction hedge : e.1 using Sym2.inductionOn with
    | _ x y =>
      rw [hedge, SimpleGraph.mem_edgeSet] at he
      change (rlc_connectorCollaredWallGraph gamma gamma').Adj
        (rlc_connectorVertexToCollared gamma gamma' x)
        (rlc_connectorVertexToCollared gamma gamma' y)
      exact rlc_connectorAugmented_adj_collared gamma gamma' he⟩

end
end StatMech.Universality
