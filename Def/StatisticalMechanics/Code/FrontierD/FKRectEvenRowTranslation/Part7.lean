/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEvenRowTranslation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedAxisSource
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEvenRowTranslation.Part6
open Set SimpleGraph StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

def fkRectEvenRowTranslationSet
    (R : FKRectTorus) (s : Nat) (S : Set R.Vertex) : Set R.Vertex :=
  fkRectEvenRowTranslationVertexEquiv R s '' S

def fkRectEvenRowTranslationSetEquiv
    (R : FKRectTorus) (s : Nat) (S : Set R.Vertex) :
    S ≃ fkRectEvenRowTranslationSet R s S where
  toFun v := ⟨fkRectEvenRowTranslationVertexEquiv R s v.1,
    ⟨v.1, v.2, rfl⟩⟩
  invFun v := ⟨(fkRectEvenRowTranslationVertexEquiv R s).symm v.1, by
    rcases v.2 with ⟨w, hw, htranslate⟩
    rw [← htranslate, Equiv.symm_apply_apply]
    exact hw⟩
  left_inv v := by
    apply Subtype.ext
    exact (fkRectEvenRowTranslationVertexEquiv R s).symm_apply_apply v.1
  right_inv v := by
    apply Subtype.ext
    exact (fkRectEvenRowTranslationVertexEquiv R s).apply_symm_apply v.1

def fkRectOpenGraphEvenRowTranslationInduceIso
    (R : FKRectTorus) (s : Nat) (hs : Even s)
    (omega : R.Configuration) (S : Set R.Vertex) :
    (fkRectOpenGraph R omega).induce S ≃g
      (fkRectOpenGraph R
        (fkRectEvenRowTranslationConfigurationEquiv R s omega)).induce
          (fkRectEvenRowTranslationSet R s S) where
  toEquiv := fkRectEvenRowTranslationSetEquiv R s S
  map_rel_iff' := by
    intro x y
    exact fkRectOpenGraph_evenRowTranslation_adj
      R s hs omega x.1 y.1

end
end StatMech.FrontierD
