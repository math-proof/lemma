/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEvenRowTranslation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedAxisSource
import Def.StatisticalMechanics.Code.FrontierD.FKRectEvenRowTranslation.Part5
open Set SimpleGraph StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkRectEvenRowTranslationConfigurationEquiv_apply
    (R : FKRectTorus) (s : Nat) (omega : R.Configuration)
    (a : R.EdgeIndex) :
    fkRectEvenRowTranslationConfigurationEquiv R s omega a =
      omega ((fkRectEvenRowTranslationEdgeEquiv R s).symm a) := rfl

theorem fkRectOpenGraph_evenRowTranslation_adj
    (R : FKRectTorus) (s : Nat) (hs : Even s)
    (omega : R.Configuration) (x y : R.Vertex) :
    (fkRectOpenGraph R
      (fkRectEvenRowTranslationConfigurationEquiv R s omega)).Adj
        (fkRectEvenRowTranslationVertexEquiv R s x)
        (fkRectEvenRowTranslationVertexEquiv R s y) ↔
      (fkRectOpenGraph R omega).Adj x y := by
  constructor
  · rintro ⟨a, haopen, ha⟩
    let b := (fkRectEvenRowTranslationEdgeEquiv R s).symm a
    refine ⟨b, haopen, ?_⟩
    have htranslate :=
      fkRectTorusIndexedEdge_evenRowTranslation R s hs b
    rw [(fkRectEvenRowTranslationEdgeEquiv R s).apply_symm_apply a,
      ha] at htranslate
    apply Sym2.map.injective
      (fkRectEvenRowTranslationVertexEquiv R s).injective
    simpa only [Sym2.map_mk] using htranslate.symm
  · rintro ⟨a, haopen, ha⟩
    refine ⟨fkRectEvenRowTranslationEdgeEquiv R s a, ?_, ?_⟩
    · change omega ((fkRectEvenRowTranslationEdgeEquiv R s).symm
        (fkRectEvenRowTranslationEdgeEquiv R s a)) = true
      rwa [(fkRectEvenRowTranslationEdgeEquiv R s).symm_apply_apply]
    · rw [fkRectTorusIndexedEdge_evenRowTranslation R s hs, ha,
        Sym2.map_mk]

end
end StatMech.FrontierD
