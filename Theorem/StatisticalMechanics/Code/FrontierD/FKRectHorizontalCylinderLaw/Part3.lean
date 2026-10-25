/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCutPushforward.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutFreeLaw.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderLaw.Part3
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

open StatMech


@[simp] theorem fkRectHorizontalCutClosedEdgeConfigEquiv_apply
    (R : FKRectTorus) (omega : FKRectHorizontalCutClosedConfig R) :
    (fkRectHorizontalCutClosedEdgeConfigEquiv R omega).1 =
      fkRectFullGraphConfiguration R omega.1 := rfl


theorem fkRectHorizontalCylinder_openSub_eq
    (R : FKRectTorus) (omega : FKRectHorizontalCutClosedConfig R) :
    FK.openSub (fkRectHorizontalCylinderGraph R)
        (fkRectHorizontalCutClosedEdgeConfigEquiv R omega).1 =
      fkRectOpenGraph R omega.1 := by
  rw [← fkOpenSub_fullGraphConfiguration R omega.1]
  apply SimpleGraph.ext
  ext x y
  simp only [FK.openSub_adj]
  constructor
  · rintro ⟨hcyl, hopen⟩
    exact ⟨(fkRectHorizontalCylinderGraph_adj_iff R x y).1 hcyl |>.1,
      hopen⟩
  · rintro ⟨htorus, hopen⟩
    refine ⟨(fkRectHorizontalCylinderGraph_adj_iff R x y).2
      ⟨htorus, ?_⟩, hopen⟩
    intro hcut
    have hfalse :=
      fkRectFullGraphConfiguration_eq_false_of_horizontalCutEdge
        R omega hcut
    rw [hfalse] at hopen
    exact Bool.noConfusion hopen


theorem fkRectHorizontalCylinder_numClusters_eq
    (R : FKRectTorus) (omega : FKRectHorizontalCutClosedConfig R) :
    FK.numClusters (fkRectHorizontalCylinderGraph R)
        (fkRectHorizontalCutClosedEdgeConfigEquiv R omega).1 =
      fkRectNumClusters R omega.1 := by
  unfold FK.numClusters fkRectNumClusters
  exact Fintype.card_congr
    (by rw [fkRectHorizontalCylinder_openSub_eq R omega])


theorem fkRectHorizontalCylinder_openCount_eq
    (R : FKRectTorus) (omega : FKRectHorizontalCutClosedConfig R) :
    FK.openCount (fkRectHorizontalCylinderGraph R)
        (fkRectHorizontalCutClosedEdgeConfigEquiv R omega).1 =
      fkRectOpenEdgeCount R omega.1 := by
  rw [fkOpenCount_eq_openSub_edgeFinset_card]
  have hfin :
      (FK.openSub (fkRectHorizontalCylinderGraph R)
          (fkRectHorizontalCutClosedEdgeConfigEquiv R omega).1).edgeFinset =
        (fkRectOpenGraph R omega.1).edgeFinset := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset]
    rw [fkRectHorizontalCylinder_openSub_eq R omega]
  rw [hfin, fkRectOpenGraph_edgeFinset_card]


theorem fkRectHorizontalCylinder_fkWeight_critical_eq
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (omega : FKRectHorizontalCutClosedConfig R) :
    FK.fkWeight (fkRectHorizontalCylinderGraph R)
        (fkRectCriticalP q) q
        (fkRectHorizontalCutClosedEdgeConfigEquiv R omega).1 =
      (1 - fkRectCriticalP q) ^
          (fkRectHorizontalCylinderGraph R).edgeFinset.card *
        fkRectCriticalReducedWeight R q omega.1 := by
  let sigma :=
    (fkRectHorizontalCutClosedEdgeConfigEquiv R omega).1
  let o := FK.openCount (fkRectHorizontalCylinderGraph R) sigma
  let c := FK.closedCount (fkRectHorizontalCylinderGraph R) sigma
  have hoc : o + c =
      (fkRectHorizontalCylinderGraph R).edgeFinset.card :=
    FK.openCount_add_closedCount
      (fkRectHorizontalCylinderGraph R) sigma
  have ho : o = fkRectOpenEdgeCount R omega.1 := by
    exact fkRectHorizontalCylinder_openCount_eq R omega
  have hp := fkRectCriticalP_eq_sqrt_mul_one_sub hq
  have hedgeProduct :
      FK.edgeProduct (fkRectHorizontalCylinderGraph R)
          (fkRectCriticalP q) sigma =
        (1 - fkRectCriticalP q) ^
            (fkRectHorizontalCylinderGraph R).edgeFinset.card *
          Real.sqrt q ^ fkRectOpenEdgeCount R omega.1 := by
    rw [FK.edgeProduct_eq_pow]
    change fkRectCriticalP q ^ o * (1 - fkRectCriticalP q) ^ c = _
    calc
      fkRectCriticalP q ^ o * (1 - fkRectCriticalP q) ^ c =
          (Real.sqrt q * (1 - fkRectCriticalP q)) ^ o *
            (1 - fkRectCriticalP q) ^ c := by
          nth_rewrite 1 [hp]
          rfl
      _ = Real.sqrt q ^ o * (1 - fkRectCriticalP q) ^ o *
            (1 - fkRectCriticalP q) ^ c := by rw [mul_pow]
      _ = (1 - fkRectCriticalP q) ^ (o + c) *
            Real.sqrt q ^ o := by
          rw [pow_add]
          ring
      _ = (1 - fkRectCriticalP q) ^
            (fkRectHorizontalCylinderGraph R).edgeFinset.card *
              Real.sqrt q ^ fkRectOpenEdgeCount R omega.1 := by
          rw [hoc, ho]
  unfold FK.fkWeight fkRectCriticalReducedWeight
  rw [hedgeProduct, fkRectHorizontalCylinder_numClusters_eq R omega]
  ring


end
end StatMech.FrontierD
