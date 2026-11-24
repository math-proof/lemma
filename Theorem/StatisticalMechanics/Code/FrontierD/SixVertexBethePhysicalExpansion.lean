module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalReduction.Part2
public import Def.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalExpansion
open Finset Matrix


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalExpansion.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

@[simp] theorem mem_sixVertexBetheCyclicIntervalTuples {n : Nat}
    (N : Nat) (x q : Fin (n + 1) -> Int) :
    q ∈ sixVertexBetheCyclicIntervalTuples N x ↔
      forall i, sixVertexBetheShiftCoordinates N x i <= q i /\ q i <= x i := by
  simp [sixVertexBetheCyclicIntervalTuples]


end
end StatMech.FrontierD
