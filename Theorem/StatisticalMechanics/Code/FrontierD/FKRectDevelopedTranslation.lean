/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedTranslation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.FKRectColumnTranslation.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedWideCrossing
open Set


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem fkRectCriticalEventMass_evenRowTranslation
    (R : FKRectTorus) (s : Nat) (hs : Even s) (q : Real)
    (A : Set R.Configuration) :
    fkRectCriticalEventMass R q A =
      fkRectCriticalEventMass R q
        ((fkRectEvenRowTranslationConfigurationEquiv R s) '' A) := by
  classical
  let C := fkRectEvenRowTranslationConfigurationEquiv R s
  unfold fkRectCriticalEventMass
  rw [← Equiv.sum_comp C (fun eta : R.Configuration =>
    (C '' A).indicator
      (fun eta => fkRectCriticalRandomClusterProb R q eta) eta)]
  apply Finset.sum_congr rfl
  intro omega _
  have hmem : C omega ∈ C '' A ↔ omega ∈ A := by
    constructor
    · rintro ⟨eta, heta, heq⟩
      exact C.injective heq ▸ heta
    · intro homega
      exact ⟨omega, homega, rfl⟩
  have hprob := fkRectCriticalRandomClusterProb_evenRowTranslation
    R s hs q omega
  by_cases hA : omega ∈ A
  · rw [Set.indicator_of_mem hA,
      Set.indicator_of_mem (hmem.mpr hA), hprob]
  · rw [Set.indicator_of_notMem hA,
      Set.indicator_of_notMem (fun h => hA (hmem.mp h))]

theorem fkRectTorusGraph_adj_columnTranslation
    (R : FKRectTorus) (s : Int) (x y : R.Vertex) :
    (fkRectTorusGraph R).Adj
        (fkRectColumnTranslationVertexEquiv R s x)
        (fkRectColumnTranslationVertexEquiv R s y) ↔
      (fkRectTorusGraph R).Adj x y := by
  constructor
  · rintro ⟨a, ha⟩
    let b := (fkRectColumnTranslationEdgeEquiv R s).symm a
    refine ⟨b, ?_⟩
    have ht := fkRectTorusIndexedEdge_columnTranslation R s b
    rw [(fkRectColumnTranslationEdgeEquiv R s).apply_symm_apply a, ha] at ht
    apply Sym2.map.injective
      (fkRectColumnTranslationVertexEquiv R s).injective
    simpa only [Sym2.map_mk] using ht.symm
  · rintro ⟨a, ha⟩
    refine ⟨fkRectColumnTranslationEdgeEquiv R s a, ?_⟩
    rw [fkRectTorusIndexedEdge_columnTranslation R s, ha, Sym2.map_mk]


theorem fkRectFullGraphConfiguration_columnTranslation
    (R : FKRectTorus) (s : Int) (omega : R.Configuration)
    (e : Sym2 R.Vertex) :
    fkRectFullGraphConfiguration R
        (fkRectColumnTranslationConfigurationEquiv R s omega)
        (Sym2.map (fkRectColumnTranslationVertexEquiv R s) e) =
      fkRectFullGraphConfiguration R omega e := by
  classical
  by_cases he : e ∈ (fkRectTorusGraph R).edgeSet
  · obtain ⟨a, ha⟩ := (mem_fkRectTorusGraph_edgeSet_iff R e).1 he
    rw [← ha, ← fkRectTorusIndexedEdge_columnTranslation,
      fkRectFullGraphConfiguration_indexedEdge,
      fkRectFullGraphConfiguration_indexedEdge]
    change omega ((fkRectColumnTranslationEdgeEquiv R s).symm
      (fkRectColumnTranslationEdgeEquiv R s a)) = omega a
    rw [(fkRectColumnTranslationEdgeEquiv R s).symm_apply_apply]
  · have htranslate :
        Sym2.map (fkRectColumnTranslationVertexEquiv R s) e ∉
          (fkRectTorusGraph R).edgeSet := by
      intro ht
      induction e using Sym2.ind with
      | _ x y =>
        simp only [Sym2.map_mk] at ht
        rw [SimpleGraph.mem_edgeSet] at ht
        apply he
        rw [SimpleGraph.mem_edgeSet]
        exact (fkRectTorusGraph_adj_columnTranslation R s x y).mp ht
    rw [fkRectFullGraphConfiguration_eq_false_of_not_edge R _ htranslate,
      fkRectFullGraphConfiguration_eq_false_of_not_edge R _ he]


theorem fkRectFullGraphConfiguration_evenRowTranslation
    (R : FKRectTorus) (s : Nat) (hs : Even s)
    (omega : R.Configuration) (e : Sym2 R.Vertex) :
    fkRectFullGraphConfiguration R
        (fkRectEvenRowTranslationConfigurationEquiv R s omega)
        (Sym2.map (fkRectEvenRowTranslationVertexEquiv R s) e) =
      fkRectFullGraphConfiguration R omega e := by
  classical
  by_cases he : e ∈ (fkRectTorusGraph R).edgeSet
  · obtain ⟨a, ha⟩ := (mem_fkRectTorusGraph_edgeSet_iff R e).1 he
    rw [← ha, ← fkRectTorusIndexedEdge_evenRowTranslation R s hs,
      fkRectFullGraphConfiguration_indexedEdge,
      fkRectFullGraphConfiguration_indexedEdge]
    change omega ((fkRectEvenRowTranslationEdgeEquiv R s).symm
      (fkRectEvenRowTranslationEdgeEquiv R s a)) = omega a
    rw [(fkRectEvenRowTranslationEdgeEquiv R s).symm_apply_apply]
  · have htranslate :
        Sym2.map (fkRectEvenRowTranslationVertexEquiv R s) e ∉
          (fkRectTorusGraph R).edgeSet := by
      intro ht
      induction e using Sym2.ind with
      | _ x y =>
        simp only [Sym2.map_mk] at ht
        rw [SimpleGraph.mem_edgeSet] at ht
        apply he
        rw [SimpleGraph.mem_edgeSet]
        exact (fkRectTorusGraph_adj_evenRowTranslation
          R s hs x y).mp ht
    rw [fkRectFullGraphConfiguration_eq_false_of_not_edge R _ htranslate,
      fkRectFullGraphConfiguration_eq_false_of_not_edge R _ he]


end
end StatMech.FrontierD
