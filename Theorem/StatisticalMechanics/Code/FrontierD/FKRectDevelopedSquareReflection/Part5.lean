/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquareReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedWideCrossing
import Theorem.StatisticalMechanics.Code.FK.TranslationInvariance.Part5
import Def.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquareReflection.Part5
open Set SimpleGraph StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkRectDevelopedReflectionConfigurationEquiv_apply
    (R : FKRectTorus) (center : Nat) (omega : R.Configuration)
    (a : R.EdgeIndex) :
    fkRectDevelopedReflectionConfigurationEquiv R center omega a =
      omega ((fkRectDevelopedReflectionEdgeEquiv R center).symm a) :=
  rfl

theorem fkRectOpenGraph_developedReflection_adj
    (R : FKRectTorus) (center : Nat) (omega : R.Configuration)
    (x y : R.Vertex) :
    (fkRectOpenGraph R
      (fkRectDevelopedReflectionConfigurationEquiv R center omega)).Adj
        (fkRectDevelopedReflectionVertexEquiv R center x)
        (fkRectDevelopedReflectionVertexEquiv R center y) ↔
      (fkRectOpenGraph R omega).Adj x y := by
  constructor
  · rintro ⟨a, haopen, ha⟩
    let b := (fkRectDevelopedReflectionEdgeEquiv R center).symm a
    refine ⟨b, ?_, ?_⟩
    · exact haopen
    · have href := fkRectTorusIndexedEdge_developedReflection R center b
      rw [(fkRectDevelopedReflectionEdgeEquiv R center).apply_symm_apply a,
        ha] at href
      have hcomp :
          (fkRectDevelopedReflectionVertexEquiv R center).symm ∘
              (fkRectDevelopedReflectionVertexEquiv R center) = id := by
        exact (fkRectDevelopedReflectionVertexEquiv R center).symm_comp_self
      have := congrArg
        (Sym2.map (fkRectDevelopedReflectionVertexEquiv R center).symm) href
      rw [Sym2.map_map, hcomp] at this
      simpa [Sym2.map_mk,
        fkRectDevelopedReflectionVertexEquiv_symm_apply] using this.symm
  · rintro ⟨b, hbopen, hb⟩
    let a := fkRectDevelopedReflectionEdgeEquiv R center b
    refine ⟨a, ?_, ?_⟩
    · change omega ((fkRectDevelopedReflectionEdgeEquiv R center).symm
          (fkRectDevelopedReflectionEdgeEquiv R center b)) = true
      rw [(fkRectDevelopedReflectionEdgeEquiv R center).symm_apply_apply]
      exact hbopen
    · rw [show a = fkRectDevelopedReflectionEdgeEquiv R center b by rfl,
        fkRectTorusIndexedEdge_developedReflection, hb]
      rfl


end
end StatMech.FrontierD
