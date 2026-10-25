/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalReduction.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalExpansion.Part13
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

def sixVertexBetheCollisionFreeTuples {n : Nat} (N : Nat)
    (x : Fin (n + 1) -> Int) : Finset (Fin (n + 1) -> Int) := by
  classical
  exact (sixVertexBetheCyclicIntervalTuples N x).filter
    (fun q => sixVertexBetheCollisionSet N x q = ∅)

def sixVertexBetheNonnegativeTuples {n : Nat} (N : Nat)
    (x : Fin (n + 1) -> Int) : Finset (Fin (n + 1) -> Int) := by
  classical
  exact (sixVertexBetheCollisionFreeTuples N x).filter (fun q => 0 ≤ q 0)

def sixVertexBetheNegativeTuples {n : Nat} (N : Nat)
    (x : Fin (n + 1) -> Int) : Finset (Fin (n + 1) -> Int) := by
  classical
  exact (sixVertexBetheCollisionFreeTuples N x).filter (fun q => q 0 < 0)

end
end StatMech.FrontierD
