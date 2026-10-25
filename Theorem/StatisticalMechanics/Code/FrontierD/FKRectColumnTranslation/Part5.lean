/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectColumnTranslation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectOrientedEvenRowBlock.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKRectColumnTranslation.Part5
open Set SimpleGraph


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkRectColumnTranslationConfigurationEquiv_apply
    (R : FKRectTorus) (s : Int) (omega : R.Configuration)
    (a : R.EdgeIndex) :
    fkRectColumnTranslationConfigurationEquiv R s omega a =
      omega ((fkRectColumnTranslationEdgeEquiv R s).symm a) := rfl

theorem fkRectOpenGraph_columnTranslation_adj
    (R : FKRectTorus) (s : Int) (omega : R.Configuration)
    (x y : R.Vertex) :
    (fkRectOpenGraph R
      (fkRectColumnTranslationConfigurationEquiv R s omega)).Adj
        (fkRectColumnTranslationVertexEquiv R s x)
        (fkRectColumnTranslationVertexEquiv R s y) ↔
      (fkRectOpenGraph R omega).Adj x y := by
  constructor
  · rintro ⟨a, haopen, ha⟩
    let b := (fkRectColumnTranslationEdgeEquiv R s).symm a
    refine ⟨b, haopen, ?_⟩
    have htranslate := fkRectTorusIndexedEdge_columnTranslation R s b
    rw [(fkRectColumnTranslationEdgeEquiv R s).apply_symm_apply a,
      ha] at htranslate
    apply Sym2.map.injective
      (fkRectColumnTranslationVertexEquiv R s).injective
    simpa only [Sym2.map_mk] using htranslate.symm
  · rintro ⟨a, haopen, ha⟩
    refine ⟨fkRectColumnTranslationEdgeEquiv R s a, ?_, ?_⟩
    · change omega ((fkRectColumnTranslationEdgeEquiv R s).symm
        (fkRectColumnTranslationEdgeEquiv R s a)) = true
      rwa [(fkRectColumnTranslationEdgeEquiv R s).symm_apply_apply]
    · rw [fkRectTorusIndexedEdge_columnTranslation R s, ha, Sym2.map_mk]

end
end StatMech.FrontierD
