/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedEndpointReflectionGlue.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedWideEndpoint.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusCrossingEvents.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedEndpointReflectionGlue
open Set


namespace StatMech.FrontierD

open StatMech.Lattice

noncomputable section

def fkRectDevelopedReflectionSet (R : FKRectTorus) (center : Nat)
    (S : Set R.Vertex) : Set R.Vertex :=
  fkRectDevelopedReflectionVertexEquiv R center '' S


def fkRectDevelopedReflectionSetEquiv (R : FKRectTorus) (center : Nat)
    (S : Set R.Vertex) : S ≃ fkRectDevelopedReflectionSet R center S where
  toFun v := ⟨fkRectDevelopedReflectionVertexEquiv R center v.1,
    ⟨v.1, v.2, rfl⟩⟩
  invFun v := ⟨fkRectDevelopedReflectionVertexEquiv R center v.1, by
    rcases v.2 with ⟨w, hw, hreflect⟩
    rw [← hreflect]
    have htwice : fkRectDevelopedReflectionVertexEquiv R center
        (fkRectDevelopedReflectionVertexEquiv R center w) = w := by
      apply Prod.ext
      · rfl
      · exact fkRectRowReflection_involutive R center w.2
    rw [htwice]
    exact hw⟩
  left_inv v := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact fkRectRowReflection_involutive R center v.1.2
  right_inv v := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact fkRectRowReflection_involutive R center v.1.2


def fkRectOpenGraphDevelopedReflectionInduceIso
    (R : FKRectTorus) (center : Nat) (omega : R.Configuration)
    (S : Set R.Vertex) :
    (fkRectOpenGraph R omega).induce S ≃g
      (fkRectOpenGraph R
        (fkRectDevelopedReflectionConfigurationEquiv R center omega)).induce
          (fkRectDevelopedReflectionSet R center S) where
  toEquiv := fkRectDevelopedReflectionSetEquiv R center S
  map_rel_iff' := by
    intro x y
    exact fkRectOpenGraph_developedReflection_adj
      R center omega x.1 y.1

end
end StatMech.FrontierD
