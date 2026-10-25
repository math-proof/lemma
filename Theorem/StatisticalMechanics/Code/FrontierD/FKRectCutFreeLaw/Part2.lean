/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutFreeLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutSquareEmbedding.Part6
import Theorem.StatisticalMechanics.Code.FK.EdgeConfigEventLaw.Part2
import Theorem.StatisticalMechanics.Code.FK.Tilt.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKRectCutFreeLaw
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

open StatMech


@[simp] theorem fkRectCutClosedEdgeConfigEquiv_apply
    (R : FKRectTorus) (omega : FKRectCutClosedConfig R) :
    (fkRectCutClosedEdgeConfigEquiv R omega).1 =
      fkRectFullGraphConfiguration R omega.1 := rfl


theorem fkRectCut_openSub_eq (R : FKRectTorus)
    (omega : FKRectCutClosedConfig R) :
    FK.openSub (fkRectCutGraph R)
        (fkRectCutClosedEdgeConfigEquiv R omega).1 =
      fkRectOpenGraph R omega.1 := by
  rw [← fkOpenSub_fullGraphConfiguration R omega.1]
  apply SimpleGraph.ext
  ext x y
  simp only [FK.openSub_adj]
  constructor
  · rintro ⟨hcut, hopen⟩
    exact ⟨(fkRectCutGraph_adj_iff R x y).1 hcut |>.1, hopen⟩
  · rintro ⟨htorus, hopen⟩
    refine ⟨(fkRectCutGraph_adj_iff R x y).2 ⟨htorus, ?_⟩, hopen⟩
    intro hcut
    have hfalse :=
      fkRectFullGraphConfiguration_forceCut_eq_false_of_cutEdge
        R omega.1 hcut
    have hforce : fkRectForceCutClosed R omega.1 = omega.1 := omega.2
    rw [hforce] at hfalse
    rw [hfalse] at hopen
    exact Bool.noConfusion hopen


theorem fkRectCut_numClusters_eq (R : FKRectTorus)
    (omega : FKRectCutClosedConfig R) :
    FK.numClusters (fkRectCutGraph R)
        (fkRectCutClosedEdgeConfigEquiv R omega).1 =
      fkRectNumClusters R omega.1 := by
  unfold FK.numClusters fkRectNumClusters
  exact Fintype.card_congr (by rw [fkRectCut_openSub_eq R omega])


theorem fkOpenCount_eq_openSub_edgeFinset_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (omega : ConfigSpace (Sym2 V)) :
    FK.openCount G omega = (FK.openSub G omega).edgeFinset.card := by
  unfold FK.openCount
  congr 1
  ext e
  rw [Finset.mem_filter, SimpleGraph.mem_edgeFinset,
    SimpleGraph.mem_edgeFinset]
  obtain ⟨⟨x, y⟩, rfl⟩ := Quot.exists_rep e
  change G.Adj x y ∧ omega s(x, y) = true ↔
    (FK.openSub G omega).Adj x y
  rfl


theorem fkRectOpenGraph_edgeFinset_card (R : FKRectTorus)
    (omega : R.Configuration) :
    (fkRectOpenGraph R omega).edgeFinset.card =
      fkRectOpenEdgeCount R omega := by
  classical
  unfold fkRectOpenEdgeCount
  symm
  apply Finset.card_bij (fun a _ => fkRectTorusIndexedEdge R a)
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    rw [SimpleGraph.mem_edgeFinset]
    obtain ⟨p, q⟩ := fkRectLiftedIndexedEdgeEnds R a
    have hproject := fkRectLiftedIndexedEdgeEnds_project R a
    rw [hproject, SimpleGraph.mem_edgeSet]
    exact ⟨a, ha, hproject⟩
  · intro a ha b hb hab
    exact fkRectTorusIndexedEdge_injective R hab
  · intro e he
    rw [SimpleGraph.mem_edgeFinset] at he
    obtain ⟨⟨x, y⟩, rfl⟩ := Quot.exists_rep e
    obtain ⟨a, ha, hedge⟩ := he
    refine ⟨a, ?_, hedge⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ha


theorem fkRectCut_openCount_eq (R : FKRectTorus)
    (omega : FKRectCutClosedConfig R) :
    FK.openCount (fkRectCutGraph R)
        (fkRectCutClosedEdgeConfigEquiv R omega).1 =
      fkRectOpenEdgeCount R omega.1 := by
  rw [fkOpenCount_eq_openSub_edgeFinset_card]
  have hfin :
      (FK.openSub (fkRectCutGraph R)
          (fkRectCutClosedEdgeConfigEquiv R omega).1).edgeFinset =
        (fkRectOpenGraph R omega.1).edgeFinset := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset]
    rw [fkRectCut_openSub_eq R omega]
  rw [hfin, fkRectOpenGraph_edgeFinset_card]


theorem fkRectCut_edgeProduct_critical_eq
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (omega : FKRectCutClosedConfig R) :
    FK.edgeProduct (fkRectCutGraph R) (fkRectCriticalP q)
        (fkRectCutClosedEdgeConfigEquiv R omega).1 =
      (1 - fkRectCriticalP q) ^ (fkRectCutGraph R).edgeFinset.card *
        Real.sqrt q ^ fkRectOpenEdgeCount R omega.1 := by
  let sigma := (fkRectCutClosedEdgeConfigEquiv R omega).1
  let o := FK.openCount (fkRectCutGraph R) sigma
  let c := FK.closedCount (fkRectCutGraph R) sigma
  have hoc : o + c = (fkRectCutGraph R).edgeFinset.card :=
    FK.openCount_add_closedCount (fkRectCutGraph R) sigma
  have ho : o = fkRectOpenEdgeCount R omega.1 := by
    dsimp only [o, sigma]
    exact fkRectCut_openCount_eq R omega
  have hp := fkRectCriticalP_eq_sqrt_mul_one_sub hq
  rw [FK.edgeProduct_eq_pow]
  change fkRectCriticalP q ^ o * (1 - fkRectCriticalP q) ^ c = _
  calc
    fkRectCriticalP q ^ o * (1 - fkRectCriticalP q) ^ c =
        (Real.sqrt q * (1 - fkRectCriticalP q)) ^ o *
          (1 - fkRectCriticalP q) ^ c := by
            nth_rewrite 1 [hp]
            rfl
    _ = Real.sqrt q ^ o * (1 - fkRectCriticalP q) ^ o *
          (1 - fkRectCriticalP q) ^ c := by
          rw [mul_pow]
    _ =
        (1 - fkRectCriticalP q) ^ (o + c) * Real.sqrt q ^ o := by
          rw [pow_add]
          ring
    _ = (1 - fkRectCriticalP q) ^
          (fkRectCutGraph R).edgeFinset.card * Real.sqrt q ^ o := by
          rw [hoc]
    _ = _ := by
      rw [ho]


theorem fkRectCut_fkWeight_critical_eq
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (omega : FKRectCutClosedConfig R) :
    FK.fkWeight (fkRectCutGraph R) (fkRectCriticalP q) q
        (fkRectCutClosedEdgeConfigEquiv R omega).1 =
      (1 - fkRectCriticalP q) ^ (fkRectCutGraph R).edgeFinset.card *
        fkRectCriticalReducedWeight R q omega.1 := by
  unfold FK.fkWeight fkRectCriticalReducedWeight
  rw [fkRectCut_edgeProduct_critical_eq R hq omega,
    fkRectCut_numClusters_eq R omega]
  ring


end
end StatMech.FrontierD
