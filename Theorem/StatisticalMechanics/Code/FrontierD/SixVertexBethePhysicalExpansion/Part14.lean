/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalReduction.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalExpansion.Part13
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem mem_sixVertexBetheNonnegativeTuples {n : Nat} (N : Nat)
    (x q : Fin (n + 1) -> Int) :
    q ∈ sixVertexBetheNonnegativeTuples N x ↔
      q ∈ sixVertexBetheCyclicIntervalTuples N x ∧
        sixVertexBetheCollisionSet N x q = ∅ ∧ 0 ≤ q 0 := by
  unfold sixVertexBetheNonnegativeTuples sixVertexBetheCollisionFreeTuples
  simp only [Finset.mem_filter]
  tauto

@[simp] theorem mem_sixVertexBetheNegativeTuples {n : Nat} (N : Nat)
    (x q : Fin (n + 1) -> Int) :
    q ∈ sixVertexBetheNegativeTuples N x ↔
      q ∈ sixVertexBetheCyclicIntervalTuples N x ∧
        sixVertexBetheCollisionSet N x q = ∅ ∧ q 0 < 0 := by
  unfold sixVertexBetheNegativeTuples sixVertexBetheCollisionFreeTuples
  simp only [Finset.mem_filter]
  tauto

end
end StatMech.FrontierD
