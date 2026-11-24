module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalReduction.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalExpansion.Part3
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

def SixVertexBetheNoAdjacent {n : Nat}
    (S : Finset (Fin (n + 1))) : Prop :=
  ∀ i, i ∈ S -> finRotate (n + 1) i ∉ S


def sixVertexBetheConstrainedCoordinateSet {n : Nat} (N : Nat)
    (x : Fin (n + 1) -> Int) (S : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) : Finset Int := by
  classical
  exact if i ∈ S then {x i}
    else if (finRotate (n + 1)).symm i ∈ S then
      {sixVertexBetheShiftCoordinates N x i}
    else Finset.Icc (sixVertexBetheShiftCoordinates N x i) (x i)

end
end StatMech.FrontierD
