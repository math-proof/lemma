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
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part83
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def RlcTwoChannelFullPhysicalRowOneOriginalParityContact {n : Int}
    (gamma' : RlcLeftDiagonalPath n) (p q p' q' a : Site 2) : Prop :=
  a = p ∨ a = p' ∨ a = q ∨ a = q' ∨
    a ∈ rlc_pathVertices gamma'.1


def RlcTwoChannelFullPhysicalRowOneBracketSourceProvenance {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (v : Site 2) : Prop :=
  (∃ w ∈ rlc_pathVertices gamma.1,
      v = rlc_dualReflect.symm w) ∨
    (∃ w ∈ (rlc_bookExteriorEndpointDetour gamma gamma').support,
      v = rlc_dualReflect.symm w) ∨
    ∃ w ∈ rlc_pathVertices gamma'.1,
      v = rlc_dualReflect.symm w


def RlcTwoChannelFullPhysicalRowOneOriginalParityIndexedContactResidue
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {omega : RlcTwoChannelEdgeConfig gamma gamma'} {u x y : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support)
    {z : Site 2} (hzRight : z ∈ rlc_pathVertices gamma.1)
    (i j : Nat) (p q p' q' : Site 2) : Prop :=
  let B := rlc_bookRowOnePhysicalTraceNetworkBracket
    gamma gamma' hzRight
  let P := RlcTwoChannelFullPhysicalRowOneOriginalParityContact
    gamma' p q p' q'
  let S := RlcTwoChannelFullPhysicalRowOneBracketSourceProvenance
    gamma gamma'
  (∃ k : Nat, k < i ∧ P (B.getVert k) ∧ S (B.getVert k)) ∨
    (∃ k : Nat, j < k ∧ k ≤ B.length ∧
      P (B.getVert k) ∧ S (B.getVert k)) ∨
    ∃ a ∈ (rlc_orderedContourArc c hx hy).support, P a


end
end StatMech.Universality
