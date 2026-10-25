/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectLocalBoxEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquare.Part11
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRightStripConnection.Part3
import Theorem.StatisticalMechanics.Code.FK.FKGeneralQConnectionSymmetry
import Def.StatisticalMechanics.Code.FrontierD.FKRectLocalBoxEmbedding.Part4
open MeasureTheory StatMech.Lattice StatMech.Percolation SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fk_twoPointFun_eq_connProb
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p q : Real) (x y : V) :
    FK.twoPointFun G p q x y = FK.connProb G p q x y := by
  rw [FK.twoPointFun_eq_sum_filter]
  rfl


theorem fkRectLocalBox_twoPoint_reflectedDiagonal_eq
    (m s : Nat) (hsm : s <= m) (p q : Real) :
    FK.twoPointFun (FK.boxGraph 2 m) p q
        (fkRectLocalBoxOrigin m)
        (fkRectLocalBoxReflectedDiagonal s m hsm) =
      FK.twoPointFun (FK.boxGraph 2 m) p q
        (fkRectLocalBoxOrigin m)
        (fkRectLocalBoxPositiveDiagonal s m hsm) := by
  rw [fk_twoPointFun_eq_connProb, fk_twoPointFun_eq_connProb]
  have hsym := FK.connProb_boxSym (FK.fkTI_signFlip 2 (1 : Fin 2))
    m p q (fkRectLocalBoxOrigin m)
      (fkRectLocalBoxPositiveDiagonal s m hsm)
  have horigin :
      (FK.fkTI_signFlip 2 (1 : Fin 2)).lift m
          (fkRectLocalBoxOrigin m) = fkRectLocalBoxOrigin m := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [FK.BoxSym.lift, FK.fkTI_signFlip, FK.fkTI_signFlipEquiv,
        fkRectLocalBoxOrigin, origin]
  have hdiag :
      (FK.fkTI_signFlip 2 (1 : Fin 2)).lift m
          (fkRectLocalBoxPositiveDiagonal s m hsm) =
        fkRectLocalBoxReflectedDiagonal s m hsm := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [FK.BoxSym.lift, FK.fkTI_signFlip, FK.fkTI_signFlipEquiv,
        fkRectLocalBoxPositiveDiagonal, fkRectPositiveDiagonalSite,
        fkRectLocalBoxReflectedDiagonal, fkRectReflectedDiagonalSite]
  rw [horigin, hdiag] at hsym
  exact hsym

@[simp] theorem fkRectLocalBoxVertex_origin
    (R : FKRectTorus) (center : R.Vertex) :
    fkRectLocalBoxVertex R center (origin 2) = center := by
  unfold fkRectLocalBoxVertex
  rw [show fkRectLocalBoxPoint R center (origin 2) =
      fkRectVertexSquarePoint R center by
        apply Prod.ext <;> simp [fkRectLocalBoxPoint, origin]]
  exact fkRectSquareRepresentativeVertex_vertexSquarePoint R center

theorem fkRectLocalBoxVertex_reflectedDiagonal_eq
    (R : FKRectTorus) (center target : R.Vertex) (s : Nat)
    (hstep : fkRectVertexSquarePoint R target -
        fkRectVertexSquarePoint R center = ((s : Int), -(s : Int))) :
    fkRectLocalBoxVertex R center (fkRectReflectedDiagonalSite s) = target := by
  unfold fkRectLocalBoxVertex
  rw [show fkRectLocalBoxPoint R center (fkRectReflectedDiagonalSite s) =
      fkRectVertexSquarePoint R target by
        apply Prod.ext
        · have h := congrArg Prod.fst hstep
          simp [fkRectLocalBoxPoint, fkRectReflectedDiagonalSite] at h ⊢
          omega
        · have h := congrArg Prod.snd hstep
          simp [fkRectLocalBoxPoint, fkRectReflectedDiagonalSite] at h ⊢
          omega]
  exact fkRectSquareRepresentativeVertex_vertexSquarePoint R target


end
end StatMech.FrontierD
