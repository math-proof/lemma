/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquarePrimitive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareGhost.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquarePrimitive
open SimpleGraph


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def FKIsingSquareFullPrimitiveCompatible
    (n : Nat) (hn : 0 < n)
    (vertexH : FKIsingSquareFullVertexNode n → Real)
    (faceH : FKIsingSquareFullFaceNode n → Real) : Prop :=
  ∀ e : FKIsingSquareInteriorRadialIncidence n hn,
    faceH (fkIsingSquareFullFaceOfRadialIncidence n hn e) -
        vertexH (fkIsingSquareInteriorRadialEndpoint n hn e) =
      fkIsingSquareInteriorRadialIncrement n hn e

def fkIsingSquareRadialPatchFullValue
    (n m : Nat) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (vertexH : FKIsingSquareFullVertexNode n → Real)
    (faceH : FKIsingSquareFullFaceNode n → Real)
    (i j : Fin m) : Real :=
  if h : Even (i.1 + j.1) then
    vertexH (fkIsingSquareRadialPatchPrimalFullVertex n m hm
      ⟨(i, j), h⟩)
  else
    faceH (fkIsingSquareRadialPatchDualFullFace n m hm hm2
      ⟨(i, j), h⟩)

end
end StatMech.Universality
