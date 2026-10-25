/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeRoots.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCoordinateBetheOne.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhase
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexBetheNoAdjacentCollisionSets (n : Nat) :
    Finset (Finset (Fin (n + 1))) := by
  classical
  exact (Finset.univ : Finset (Fin (n + 1))).powerset.filter
    SixVertexBetheNoAdjacent

def sixVertexBetheZeroPhaseRegularizedIntervalSum
    {n : Nat} (N : Nat) (c : Real) (p : Fin (n + 1) -> Real)
    (x : Fin (n + 1) -> Int) (ell : Fin (n + 1)) : Complex := by
  classical
  exact ∑ S ∈ sixVertexBetheNoAdjacentCollisionSets n,
    (-1 : Complex) ^ S.card *
      ((if ell ∈ S then 1
        else if (finRotate (n + 1)).symm ell ∈ S then 1
        else 2 +
          ((x ell - sixVertexBetheShiftCoordinates N x ell - 1).toNat :
            Complex) * (c : Complex) ^ 2) *
        ∏ i ∈ (Finset.univ.erase ell),
          ∑ y ∈ sixVertexBetheConstrainedCoordinateSet N x S i,
            (if y = sixVertexBetheShiftCoordinates N x i ∨ y = x i
              then 1 else (c : Complex) ^ 2) *
              sixVertexBethePhase (p i) ^ y)


end
end StatMech.FrontierD
