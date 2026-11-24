module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalReduction.Part2
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

def sixVertexBetheCyclicIntervalTuples {n : Nat} (N : Nat)
    (x : Fin (n + 1) -> Int) : Finset (Fin (n + 1) -> Int) :=
  Fintype.piFinset fun i =>
    Finset.Icc (sixVertexBetheShiftCoordinates N x i) (x i)

end
end StatMech.FrontierD
