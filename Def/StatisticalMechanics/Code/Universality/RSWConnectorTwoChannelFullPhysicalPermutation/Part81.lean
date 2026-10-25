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
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part81
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def RlcTwoChannelFullPhysicalRowOneSelectedPrimalFlankContactConclusion
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u x y a b p p' : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support)
    {z : Site 2} (hzRight : z ∈ rlc_pathVertices gamma.1)
    (H : (hypercubicLattice 2).Walk a b)
    (W : (hypercubicLattice 2).Walk p p') : Prop :=
  (∃ v ∈ W.support, v ∈ H.support) ∨
    (∃ v ∈ W.support,
      v ∈ (rlc_bookRowOnePhysicalTraceNetworkBracket
        gamma gamma' hzRight).support ∧ (v = p ∨ v = p')) ∨
    (∃ v ∈ W.support,
      v ∈ (rlc_bookRowOnePhysicalTraceNetworkBracket
        gamma gamma' hzRight).support ∧ v ∈ c.support) ∨
    ((∃ v ∈ W.support,
        v ∈ (rlc_orderedContourArc c hx hy).support) ∧
      ∃ v ∈ W.support,
        v ∈ (rlc_complementaryContourArc c hx hy).support)


end
end StatMech.Universality
