/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceJordan.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourFinal.Part4
import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part22
import Theorem.StatisticalMechanics.Code.Walls.fwrfaceregion.Part3
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part45
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

def RlcCentralFacePairedFirstIntersectionSideData {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (u u' : Site 2) : Prop :=
  (∃ (z : Site 2)
      (hz : z ∈ ((rlc_ambientCrossingWalk gamma'.1).map
        rlc_flipXLatticeHom).support)
      (b : Site 2),
      z ∈ rlc_pathVertices gamma.1 ∧
        rlc_flipX z ∈ rlc_pathVertices gamma'.1 ∧
        rlc_dualReflect b ∈
          ((rlc_ambientCrossingWalk gamma'.1).map
            rlc_flipXLatticeHom).support ∧
        rlc_dualReflect u' ∈
          ((rlc_ambientCrossingWalk gamma'.1).map
            rlc_flipXLatticeHom).support ∧
        (rlc_dualReflect b ∈
            (((rlc_ambientCrossingWalk gamma'.1).map
              rlc_flipXLatticeHom).dropUntil z hz).support ↔
          rlc_dualReflect u' ∈
            (((rlc_ambientCrossingWalk gamma'.1).map
              rlc_flipXLatticeHom).dropUntil z hz).support)) ∧
    ∃ (z : Site 2)
      (hz : rlc_flipX z ∈
        (((rlc_ambientCrossingWalk gamma.1).map
          rlc_flipXLatticeHom).reverse).support)
      (b : Site 2),
      z ∈ rlc_pathVertices gamma.1 ∧
        rlc_flipX z ∈ rlc_pathVertices gamma'.1 ∧
        rlc_dualReflect b ∈
          (((rlc_ambientCrossingWalk gamma.1).map
            rlc_flipXLatticeHom).reverse).support ∧
        rlc_dualReflect u ∈
          (((rlc_ambientCrossingWalk gamma.1).map
            rlc_flipXLatticeHom).reverse).support ∧
        (rlc_dualReflect b ∈
            ((((rlc_ambientCrossingWalk gamma.1).map
              rlc_flipXLatticeHom).reverse).dropUntil
                (rlc_flipX z) hz).support ↔
          rlc_dualReflect u ∈
            ((((rlc_ambientCrossingWalk gamma.1).map
              rlc_flipXLatticeHom).reverse).dropUntil
                (rlc_flipX z) hz).support)


end
end StatMech.Universality
