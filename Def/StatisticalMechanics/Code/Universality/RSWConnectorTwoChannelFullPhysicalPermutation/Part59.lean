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
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part58
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def RlcTwoChannelFullPhysicalOrderedWallFamilyOutcome {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {z x y ur ul : Site 2}
    (flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2))
    (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur)
    (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul) : Prop :=
  (((∀ e ∈ qr.edges,
        Sym2.map rlc_dualReflect e ∈
          rlc_reflectedPathEdges gamma'.1) ∧
      rlc_dualReflect x = z ∧
      (∀ e ∈ ql.edges,
        Sym2.map rlc_dualReflect e ∈
          rlc_reflectedPathEdges gamma'.1) ∧
      rlc_dualReflect y = (gamma'.1.2.1 : Site 2)) ∧
    (let W := (rlc_ambientCrossingWalk gamma'.1).map
        rlc_flipXLatticeHom;
      W.support.idxOf (rlc_dualReflect ur) <
        W.support.idxOf (rlc_dualReflect ul))) ∨
  ((∀ e ∈ qr.edges,
      Sym2.map rlc_dualReflect e ∈
        rlc_reflectedPathEdges gamma'.1) ∧
    rlc_dualReflect x = z ∧
    (∀ e ∈ ql.edges,
      Sym2.map rlc_dualReflect e ∈
        rlc_reflectedPathEdges gamma.1) ∧
    ∃ r ∈ rlc_pathVertices gamma.1,
      rlc_dualReflect y = rlc_flipX r ∧ r ∈ flipLeft.support) ∨
  (((∀ e ∈ qr.edges,
        Sym2.map rlc_dualReflect e ∈
          rlc_reflectedPathEdges gamma.1) ∧
      rlc_dualReflect x = (gamma.1.1 : Site 2) ∧
      (∀ e ∈ ql.edges,
        Sym2.map rlc_dualReflect e ∈
          rlc_reflectedPathEdges gamma'.1) ∧
      rlc_dualReflect y = (gamma'.1.2.1 : Site 2)) ∧
    ∃ (hzR : rlc_flipX z ∈
          (((rlc_ambientCrossingWalk gamma.1).map
            rlc_flipXLatticeHom).reverse).support)
      (hzL : z ∈ ((rlc_ambientCrossingWalk gamma'.1).map
        rlc_flipXLatticeHom).support),
      rlc_dualReflect ur ∈
          ((((rlc_ambientCrossingWalk gamma.1).map
            rlc_flipXLatticeHom).reverse).dropUntil
              (rlc_flipX z) hzR).support ∧
        rlc_dualReflect ul ∈
          (((rlc_ambientCrossingWalk gamma'.1).map
            rlc_flipXLatticeHom).dropUntil z hzL).support) ∨
  ∃ r : Site 2,
    (∀ e ∈ qr.edges,
      Sym2.map rlc_dualReflect e ∈
        rlc_reflectedPathEdges gamma.1) ∧
    rlc_dualReflect x = (gamma.1.1 : Site 2) ∧
    (∀ e ∈ ql.edges,
      Sym2.map rlc_dualReflect e ∈
        rlc_reflectedPathEdges gamma.1) ∧
    r ∈ rlc_pathVertices gamma.1 ∧
    rlc_dualReflect y = rlc_flipX r ∧
    r ∈ flipLeft.support ∧
    (let W := ((rlc_ambientCrossingWalk gamma.1).map
        rlc_flipXLatticeHom).reverse;
      W.support.idxOf (rlc_dualReflect ul) <
        W.support.idxOf (rlc_dualReflect ur))


end
end StatMech.Universality
