/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectColumnTranslation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectOrientedEvenRowBlock.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKRectColumnTranslation.Part4
open Set SimpleGraph


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkRectColumnTranslationEdgeEquiv_apply
    (R : FKRectTorus) (s : Int) (a : R.EdgeIndex) :
    fkRectColumnTranslationEdgeEquiv R s a =
      (a.1, (fkRectColumnTranslate R s a.2.1, a.2.2)) := rfl


theorem fkRectTorusIndexedEdge_columnTranslation
    (R : FKRectTorus) (s : Int) (a : R.EdgeIndex) :
    fkRectTorusIndexedEdge R
        (fkRectColumnTranslationEdgeEquiv R s a) =
      Sym2.map (fkRectColumnTranslationVertexEquiv R s)
        (fkRectTorusIndexedEdge R a) := by
  rcases a with ⟨b, x, y⟩
  cases b
  · by_cases hy : Even y.val
    · simp only [fkRectColumnTranslationEdgeEquiv_apply,
        fkRectTorusIndexedEdge, Bool.false_eq_true, if_false, hy, if_true,
        fkRectColumnTranslationVertexEquiv_apply, Sym2.map_mk]
      rw [fkRectColumnTranslate_cyclicPred]
    · simp only [fkRectColumnTranslationEdgeEquiv_apply,
        fkRectTorusIndexedEdge, Bool.false_eq_true, if_false, hy,
        fkRectColumnTranslationVertexEquiv_apply, Sym2.map_mk]
      rw [fkRectColumnTranslate_cyclicPred]
  · simp [fkRectTorusIndexedEdge]


end
end StatMech.FrontierD
