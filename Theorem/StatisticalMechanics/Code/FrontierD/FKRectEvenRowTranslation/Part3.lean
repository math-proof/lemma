/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEvenRowTranslation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedAxisSource
import Def.StatisticalMechanics.Code.FrontierD.FKRectEvenRowTranslation.Part3
open Set SimpleGraph StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkRectEvenRowTranslationVertexEquiv_apply
    (R : FKRectTorus) (s : Nat) (v : R.Vertex) :
    fkRectEvenRowTranslationVertexEquiv R s v =
      (v.1, fkRectRowTranslate R s v.2) := rfl

theorem fkRectEvenRowTranslationVertexEquiv_add
    (R : FKRectTorus) (a b : Nat) (v : R.Vertex) :
    fkRectEvenRowTranslationVertexEquiv R a
        (fkRectEvenRowTranslationVertexEquiv R b v) =
      fkRectEvenRowTranslationVertexEquiv R (a + b) v := by
  apply Prod.ext
  · rfl
  · exact fkRectRowTranslate_add R a b v.2

@[simp] theorem fkRectEvenRowTranslationVertexEquiv_zero
    (R : FKRectTorus) (v : R.Vertex) :
    fkRectEvenRowTranslationVertexEquiv R 0 v = v := by
  apply Prod.ext
  · rfl
  · exact fkRectRowTranslate_zero R v.2


end
end StatMech.FrontierD
