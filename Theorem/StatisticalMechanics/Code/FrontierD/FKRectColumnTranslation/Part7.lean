/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectColumnTranslation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectOrientedEvenRowBlock.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKRectColumnTranslation.Part7
open Set SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectConnectedWithin_columnTranslation_iff
    (R : FKRectTorus) (s : Int) (omega : R.Configuration)
    (S : Set R.Vertex) (x y : S) :
    FKRectConnectedWithin R
        (fkRectColumnTranslationConfigurationEquiv R s omega)
        (fkRectColumnTranslationSet R s S)
        (fkRectColumnTranslationSetEquiv R s S x)
        (fkRectColumnTranslationSetEquiv R s S y) ↔
      FKRectConnectedWithin R omega S x y := by
  exact (fkRectOpenGraphColumnTranslationInduceIso
    R s omega S).reachable_iff

theorem fkRectCritical_connectedWithinMass_columnTranslation
    (R : FKRectTorus) (s : Int) (q : Real)
    (S : Set R.Vertex) (x y : S) :
    fkRectCriticalEventMass R q
        {omega | FKRectConnectedWithin R omega
          (fkRectColumnTranslationSet R s S)
          (fkRectColumnTranslationSetEquiv R s S x)
          (fkRectColumnTranslationSetEquiv R s S y)} =
      fkRectCriticalEventMass R q
        {omega | FKRectConnectedWithin R omega S x y} := by
  classical
  let C := fkRectColumnTranslationConfigurationEquiv R s
  let A : Set R.Configuration :=
    {omega | FKRectConnectedWithin R omega S x y}
  let B : Set R.Configuration :=
    {omega | FKRectConnectedWithin R omega
      (fkRectColumnTranslationSet R s S)
      (fkRectColumnTranslationSetEquiv R s S x)
      (fkRectColumnTranslationSetEquiv R s S y)}
  unfold fkRectCriticalEventMass
  rw [← Equiv.sum_comp C (fun eta =>
    B.indicator (fun eta => fkRectCriticalRandomClusterProb R q eta) eta)]
  apply Finset.sum_congr rfl
  intro omega _
  have hmem : C omega ∈ B ↔ omega ∈ A :=
    fkRectConnectedWithin_columnTranslation_iff R s omega S x y
  have hprob : fkRectCriticalRandomClusterProb R q (C omega) =
      fkRectCriticalRandomClusterProb R q omega :=
    fkRectCriticalRandomClusterProb_columnTranslation R s q omega
  by_cases hA : omega ∈ A
  · rw [Set.indicator_of_mem hA,
      Set.indicator_of_mem (hmem.mpr hA), hprob]
  · rw [Set.indicator_of_notMem hA,
      Set.indicator_of_notMem (fun hB => hA (hmem.mp hB))]


theorem fkRectTorusIndexedEdge_columnSucc (R : FKRectTorus)
    (a : R.EdgeIndex) :
    fkRectTorusIndexedEdge R
        (fkRectColumnTranslationEdgeEquiv R 1 a) =
      Sym2.map (fkRectColumnTranslationVertexEquiv R 1)
        (fkRectTorusIndexedEdge R a) :=
  fkRectTorusIndexedEdge_columnTranslation R 1 a

theorem fkRectTorusGraph_adj_columnSucc (R : FKRectTorus)
    (x y : R.Vertex) :
    (fkRectTorusGraph R).Adj
        (fkRectColumnTranslationVertexEquiv R 1 x)
        (fkRectColumnTranslationVertexEquiv R 1 y) ↔
      (fkRectTorusGraph R).Adj x y := by
  constructor
  · rintro ⟨a, ha⟩
    let b := (fkRectColumnTranslationEdgeEquiv R 1).symm a
    refine ⟨b, ?_⟩
    have htranslate := fkRectTorusIndexedEdge_columnSucc R b
    rw [(fkRectColumnTranslationEdgeEquiv R 1).apply_symm_apply a,
      ha] at htranslate
    apply Sym2.map.injective
      (fkRectColumnTranslationVertexEquiv R 1).injective
    simpa only [Sym2.map_mk] using htranslate.symm
  · rintro ⟨a, ha⟩
    refine ⟨fkRectColumnTranslationEdgeEquiv R 1 a, ?_⟩
    rw [fkRectTorusIndexedEdge_columnSucc R, ha, Sym2.map_mk]

theorem fkRectOpenGraph_columnSucc_adj
    (R : FKRectTorus) (omega : R.Configuration) (x y : R.Vertex) :
    (fkRectOpenGraph R
      (fkRectColumnTranslationConfigurationEquiv R 1 omega)).Adj
        (fkRectColumnTranslationVertexEquiv R 1 x)
        (fkRectColumnTranslationVertexEquiv R 1 y) ↔
      (fkRectOpenGraph R omega).Adj x y :=
  fkRectOpenGraph_columnTranslation_adj R 1 omega x y

theorem fkRectCriticalRandomClusterProb_columnSucc
    (R : FKRectTorus) (q : Real) (omega : R.Configuration) :
    fkRectCriticalRandomClusterProb R q
        (fkRectColumnTranslationConfigurationEquiv R 1 omega) =
      fkRectCriticalRandomClusterProb R q omega :=
  fkRectCriticalRandomClusterProb_columnTranslation R 1 q omega

theorem fkRectConnectedWithin_columnSucc_iff
    (R : FKRectTorus) (omega : R.Configuration)
    (S : Set R.Vertex) (x y : S) :
    FKRectConnectedWithin R
        (fkRectColumnTranslationConfigurationEquiv R 1 omega)
        (fkRectColumnTranslationSet R 1 S)
        (fkRectColumnTranslationSetEquiv R 1 S x)
        (fkRectColumnTranslationSetEquiv R 1 S y) ↔
      FKRectConnectedWithin R omega S x y :=
  fkRectConnectedWithin_columnTranslation_iff R 1 omega S x y

theorem fkRectCritical_connectedWithinMass_columnSucc
    (R : FKRectTorus) (q : Real) (S : Set R.Vertex) (x y : S) :
    fkRectCriticalEventMass R q
        {omega | FKRectConnectedWithin R omega
          (fkRectColumnTranslationSet R 1 S)
          (fkRectColumnTranslationSetEquiv R 1 S x)
          (fkRectColumnTranslationSetEquiv R 1 S y)} =
      fkRectCriticalEventMass R q
        {omega | FKRectConnectedWithin R omega S x y} :=
  fkRectCritical_connectedWithinMass_columnTranslation R 1 q S x y


end
end StatMech.FrontierD
