/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFibreCube.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CollaredWalkCrossing
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangFaithfulExclusive.Part2
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part82
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def RlcTwoChannelFullPhysicalRowOneCleanExactSourceSpliceEdgeResidue
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (A B : Set (RlcConnectorVertex n))
    {u a b : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Walk u u)
    (H : (hypercubicLattice 2).Walk a b)
    (ur vr ul vl : Site 2) {p p' : Site 2}
    (w : (hypercubicLattice 2).Walk p p')
    (f g : Site 2) : Prop :=
  (s(f, g) = s(ur, vr) ∧
      RlcTwoChannelFullPhysicalReflectedLeftTerminalCleanSeparatorContact
        gamma gamma' A B c H ur vr) ∨
    (s(f, g) = s(ul, vl) ∧
      RlcTwoChannelFullPhysicalReflectedLeftTerminalCleanSeparatorContact
        gamma gamma' A B c H ul vl) ∨
    (s(f, g) = s(vr, phb_doubleDualShift p) ∨
      s(f, g) = s(ur, phb_doubleDualShift p)) ∨
    (∃ e₀ ∈ w.edges,
      Sym2.map phb_doubleDualShift e₀ = s(f, g) ∧
        rlc_twoChannelFullAmbientConfig gamma gamma'
          (rlc_twoChannelFullPhysicalCutInteriorConfig
            gamma gamma' A) e₀ = true ∧
        ((∃ source :
            (rlc_connectorTwoChannelGraph gamma gamma').edgeSet,
            source.1.map Subtype.val = e₀) ∨
          e₀ ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) ∧
        e₀ ∈ rlc_connectorCentralFacePlanarEdges gamma gamma' ∧
        rlc_twoChannelFullPhysicalEdgeCrossesCut
          (rlc_twoChannelFullPhysicalLiftVertexCut B)
            (Sym2.map rlc_flipX e₀) ∧
        ∃ target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet,
          target.1.map Subtype.val = Sym2.map rlc_flipX e₀ ∧
            ((¬Nonempty (RlcTwoChannelAmbientSourceEdge gamma gamma'
                (rlc_pimsEdgeEquiv (target.1.map Subtype.val)))) ∨
              ∃ physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
                physical.1 = target ∧
                  ¬rlc_twoChannelFullPhysicalEdgeCrossesCut A
                    (rlc_twoChannelFullPhysicalSourceEdge physical).1)) ∨
    (s(f, g) = s(vl, phb_doubleDualShift p') ∨
      s(f, g) = s(ul, phb_doubleDualShift p'))


end
end StatMech.Universality
