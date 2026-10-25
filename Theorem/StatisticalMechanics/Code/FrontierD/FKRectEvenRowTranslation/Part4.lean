/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEvenRowTranslation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedAxisSource
import Def.StatisticalMechanics.Code.FrontierD.FKRectEvenRowTranslation.Part4
open Set SimpleGraph StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkRectEvenRowTranslationEdgeEquiv_apply
    (R : FKRectTorus) (s : Nat) (a : R.EdgeIndex) :
    fkRectEvenRowTranslationEdgeEquiv R s a =
      (a.1, (a.2.1, fkRectRowTranslate R s a.2.2)) := rfl


theorem fkRectTorusIndexedEdge_evenRowTranslation
    (R : FKRectTorus) (s : Nat) (hs : Even s) (a : R.EdgeIndex) :
    fkRectTorusIndexedEdge R
        (fkRectEvenRowTranslationEdgeEquiv R s a) =
      Sym2.map (fkRectEvenRowTranslationVertexEquiv R s)
        (fkRectTorusIndexedEdge R a) := by
  rcases a with ⟨b, x, y⟩
  cases b
  · have hparity := fkRectRowTranslate_even_iff R s hs y
    by_cases hy : Even y.val
    · have hty : Even (fkRectRowTranslate R s y).val := hparity.mpr hy
      simp only [fkRectEvenRowTranslationEdgeEquiv_apply,
        fkRectTorusIndexedEdge, Bool.false_eq_true, if_false, hy, hty,
        if_true, fkRectEvenRowTranslationVertexEquiv_apply, Sym2.map_mk]
      rw [fkRectRowTranslate_cyclicPred]
    · have hty : ¬ Even (fkRectRowTranslate R s y).val := by
        simpa [hparity] using hy
      simp only [fkRectEvenRowTranslationEdgeEquiv_apply,
        fkRectTorusIndexedEdge, Bool.false_eq_true, if_false, hy, hty,
        fkRectEvenRowTranslationVertexEquiv_apply, Sym2.map_mk]
      rw [fkRectRowTranslate_cyclicPred]
  · simp only [fkRectEvenRowTranslationEdgeEquiv_apply,
      fkRectTorusIndexedEdge, if_true,
      fkRectEvenRowTranslationVertexEquiv_apply, Sym2.map_mk]
    rw [fkRectRowTranslate_cyclicPred]


theorem fkRectTorusGraph_adj_evenRowTranslation
    (R : FKRectTorus) (s : Nat) (hs : Even s) (x y : R.Vertex) :
    (fkRectTorusGraph R).Adj
        (fkRectEvenRowTranslationVertexEquiv R s x)
        (fkRectEvenRowTranslationVertexEquiv R s y) ↔
      (fkRectTorusGraph R).Adj x y := by
  constructor
  · rintro ⟨a, ha⟩
    let b := (fkRectEvenRowTranslationEdgeEquiv R s).symm a
    refine ⟨b, ?_⟩
    have htranslate :=
      fkRectTorusIndexedEdge_evenRowTranslation R s hs b
    rw [(fkRectEvenRowTranslationEdgeEquiv R s).apply_symm_apply a,
      ha] at htranslate
    apply Sym2.map.injective
      (fkRectEvenRowTranslationVertexEquiv R s).injective
    simpa only [Sym2.map_mk] using htranslate.symm
  · rintro ⟨a, ha⟩
    refine ⟨fkRectEvenRowTranslationEdgeEquiv R s a, ?_⟩
    rw [fkRectTorusIndexedEdge_evenRowTranslation R s hs, ha,
      Sym2.map_mk]


end
end StatMech.FrontierD
