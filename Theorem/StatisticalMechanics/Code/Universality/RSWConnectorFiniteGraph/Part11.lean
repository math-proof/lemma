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
public import Def.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part14
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

theorem rlc_pimsEdgeEquiv_mem_connectorPIMSExteriorPreimages {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {e : Sym2 (Site 2)}
    (htarget : e ∈ rlc_connectorEdges gamma gamma')
    (hsource : rlc_pimsEdgeEquiv e ∉ rlc_connectorEdges gamma gamma')
    (htrace : rlc_pimsEdgeEquiv e ∉
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
    rlc_pimsEdgeEquiv e ∈
      rlc_connectorPIMSExteriorPreimages gamma gamma' := by
  rw [rlc_connectorPIMSExteriorPreimages, Finset.mem_sdiff]
  refine ⟨Finset.mem_image.mpr ⟨e, htarget, rfl⟩, ?_⟩
  rw [Finset.mem_union]
  exact not_or_intro hsource htrace


end
end StatMech.Universality
