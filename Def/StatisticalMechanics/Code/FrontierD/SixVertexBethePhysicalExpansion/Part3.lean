/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalReduction.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalExpansion.Part2
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

def sixVertexBetheIntervalTupleWeight {n : Nat} (N : Nat) (c : Real)
    (z : Fin (n + 1) -> Complex) (x q : Fin (n + 1) -> Int) : Complex :=
  ∏ i, 
    (if q i = sixVertexBetheShiftCoordinates N x i \/ q i = x i
      then 1 else (c : Complex) ^ 2) * z i ^ q i


def sixVertexBetheCollisionFreeIntervalSum {n : Nat} (N : Nat) (c : Real)
    (z : Fin (n + 1) -> Complex) (x : Fin (n + 1) -> Int) : Complex := by
  classical
  exact ∑ q ∈ (sixVertexBetheCyclicIntervalTuples N x).filter
      (fun q => sixVertexBetheCollisionSet N x q = ∅),
    sixVertexBetheIntervalTupleWeight N c z x q


def sixVertexBetheCollisionConstrainedIntervalSum {n : Nat} (N : Nat)
    (c : Real) (z : Fin (n + 1) -> Complex) (x : Fin (n + 1) -> Int)
    (S : Finset (Fin (n + 1))) : Complex := by
  classical
  exact ∑ q ∈ (sixVertexBetheCyclicIntervalTuples N x).filter
      (fun q => S ⊆ sixVertexBetheCollisionSet N x q),
    sixVertexBetheIntervalTupleWeight N c z x q

end
end StatMech.FrontierD
