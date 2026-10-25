/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectColumnTranslation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectOrientedEvenRowBlock.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectColumnTranslation.Part6
open Set SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def fkRectColumnTranslationSet
    (R : FKRectTorus) (s : Int) (S : Set R.Vertex) : Set R.Vertex :=
  fkRectColumnTranslationVertexEquiv R s '' S


def fkRectColumnTranslationSetEquiv
    (R : FKRectTorus) (s : Int) (S : Set R.Vertex) :
    S ≃ fkRectColumnTranslationSet R s S where
  toFun v := ⟨fkRectColumnTranslationVertexEquiv R s v.1,
    ⟨v.1, v.2, rfl⟩⟩
  invFun v := ⟨(fkRectColumnTranslationVertexEquiv R s).symm v.1, by
    rcases v.2 with ⟨w, hw, htranslate⟩
    rw [← htranslate, Equiv.symm_apply_apply]
    exact hw⟩
  left_inv v := by
    apply Subtype.ext
    exact (fkRectColumnTranslationVertexEquiv R s).symm_apply_apply v.1
  right_inv v := by
    apply Subtype.ext
    exact (fkRectColumnTranslationVertexEquiv R s).apply_symm_apply v.1

def fkRectOpenGraphColumnTranslationInduceIso
    (R : FKRectTorus) (s : Int) (omega : R.Configuration)
    (S : Set R.Vertex) :
    (fkRectOpenGraph R omega).induce S ≃g
      (fkRectOpenGraph R
        (fkRectColumnTranslationConfigurationEquiv R s omega)).induce
          (fkRectColumnTranslationSet R s S) where
  toEquiv := fkRectColumnTranslationSetEquiv R s S
  map_rel_iff' := by
    intro x y
    exact fkRectOpenGraph_columnTranslation_adj R s omega x.1 y.1

end
end StatMech.FrontierD
