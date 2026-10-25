/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquareReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedWideCrossing
import Theorem.StatisticalMechanics.Code.FK.TranslationInvariance.Part5
import Def.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquareReflection.Part3
open Set SimpleGraph StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkRectDevelopedReflectionVertexEquiv_apply
    (R : FKRectTorus) (center : Nat) (v : R.Vertex) :
    fkRectDevelopedReflectionVertexEquiv R center v =
      (v.1, fkRectRowReflection R center v.2) :=
  rfl

theorem fkRectSquareUndevelopPoint_developedSwap
    (n : Nat) (z : Site 2) :
    fkRectSquareUndevelopPoint
        (fkRectDevelopedSquarePoint n (StatMech.Universality.crf_swap z)) =
      let p := fkRectSquareUndevelopPoint (fkRectDevelopedSquarePoint n z)
      (p.1, 2 * (n : Int) - p.2) := by
  apply Prod.ext <;>
    simp [fkRectSquareUndevelopPoint, fkRectDevelopedSquarePoint,
      StatMech.Universality.crf_swap, StatMech.Universality.crf_swapFun] <;>
    omega


theorem fkRectDevelopedReflectionVertex_developedSquareVertex
    (R : FKRectTorus) (n : Nat) (z : Site 2) :
    fkRectDevelopedReflectionVertexEquiv R n
        (fkRectDevelopedSquareVertex R n z) =
      fkRectDevelopedSquareVertex R n
        (StatMech.Universality.crf_swap z) := by
  have hrepr (p : Int × Int) :
      fkRectSquareRepresentativeVertex R p =
        fkRectLiftedVertex R (fkRectSquareUndevelopPoint p) := by
    rw [← fkRectSquareRepresentativeVertex_developPoint]
    rw [fkRectSquareDevelopPoint_undevelopPoint]
  rw [fkRectDevelopedSquareVertex, fkRectDevelopedSquareVertex,
    hrepr, hrepr, fkRectDevelopedReflectionVertexEquiv_apply,
    fkRectSquareUndevelopPoint_developedSwap]
  apply Prod.ext
  · rfl
  · exact fkRectRowReflection_intModFin R n _


end
end StatMech.FrontierD
