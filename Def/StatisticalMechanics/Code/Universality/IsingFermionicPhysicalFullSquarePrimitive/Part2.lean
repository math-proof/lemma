/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquarePrimitive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareGhost.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquarePrimitive.Part2
open SimpleGraph


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareRadialPatchFullValueNat
    (n m : Nat) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (vertexH : FKIsingSquareFullVertexNode n → Real)
    (faceH : FKIsingSquareFullFaceNode n → Real) : Nat → Nat → Real :=
  fun i j ↦
    if hi : i < m then
      if hj : j < m then
        fkIsingSquareRadialPatchFullValue
          n m hm hm2 vertexH faceH ⟨i, hi⟩ ⟨j, hj⟩
      else 0
    else 0

end
end StatMech.Universality
