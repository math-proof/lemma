/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterFKG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterGraphBridge.Part10
import Theorem.StatisticalMechanics.Code.FK.PositiveAssociation
import Def.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterFKG
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

open StatMech

@[simp] theorem fkRectGraphConfigurationExtend_edge
    (R : FKRectTorus) (eta : FKRectGraphConfiguration R)
    (e : {e // e ∈ (fkRectTorusGraph R).edgeSet}) :
    fkRectGraphConfigurationExtend R eta e.1 = eta e := by
  simp [fkRectGraphConfigurationExtend, e.2]


theorem fk_openSub_configurationExtend
    (R : FKRectTorus) (eta : FKRectGraphConfiguration R) :
    FK.openSub (fkRectTorusGraph R)
        (fkRectGraphConfigurationExtend R eta) =
      fkRectGraphOpenGraph R eta := by
  ext x y
  constructor
  · rintro ⟨hxy, hopen⟩
    have he : s(x, y) ∈ (fkRectTorusGraph R).edgeSet := by
      rw [SimpleGraph.mem_edgeSet]
      exact hxy
    refine ⟨⟨s(x, y), he⟩, ?_, rfl⟩
    simpa [fkRectGraphConfigurationExtend, he] using hopen
  · rintro ⟨e, hopen, hexy⟩
    have hedge : (fkRectTorusGraph R).Adj x y := by
      have he := e.2
      rw [hexy, SimpleGraph.mem_edgeSet] at he
      exact he
    refine ⟨hedge, ?_⟩
    rw [fkRectGraphConfigurationExtend]
    simp only [hedge, SimpleGraph.mem_edgeSet, dite_true]
    have hsub : (⟨s(x, y), by
        rwa [SimpleGraph.mem_edgeSet]⟩ :
          {e // e ∈ (fkRectTorusGraph R).edgeSet}) = e := by
      apply Subtype.ext
      exact hexy.symm
    simpa [hsub] using hopen


theorem fk_numClusters_configurationExtend
    (R : FKRectTorus) (eta : FKRectGraphConfiguration R) :
    FK.numClusters (fkRectTorusGraph R)
        (fkRectGraphConfigurationExtend R eta) =
      Fintype.card (fkRectGraphOpenGraph R eta).ConnectedComponent := by
  unfold FK.numClusters
  simpa only [← Nat.card_eq_fintype_card] using congrArg
    (fun G : SimpleGraph R.Vertex => Nat.card G.ConnectedComponent)
    (fk_openSub_configurationExtend R eta)


theorem fk_edgeProduct_configurationExtend
    (R : FKRectTorus) (p : Real) (eta : FKRectGraphConfiguration R) :
    FK.edgeProduct (fkRectTorusGraph R) p
        (fkRectGraphConfigurationExtend R eta) =
      ∏ e : {e // e ∈ (fkRectTorusGraph R).edgeSet},
        if eta e then p else 1 - p := by
  unfold FK.edgeProduct
  let edgeEquiv :
      {e // e ∈ (fkRectTorusGraph R).edgeFinset} ≃
        {e // e ∈ (fkRectTorusGraph R).edgeSet} :=
    Equiv.subtypeEquiv (Equiv.refl _) fun e =>
      SimpleGraph.mem_edgeFinset
  calc
    (∏ e ∈ (fkRectTorusGraph R).edgeFinset,
        if fkRectGraphConfigurationExtend R eta e then p else 1 - p) =
        ∏ e : {e // e ∈ (fkRectTorusGraph R).edgeFinset},
          if fkRectGraphConfigurationExtend R eta e.1 then p else 1 - p := by
      rw [← Finset.prod_attach, Finset.attach_eq_univ]
    _ = ∏ e : {e // e ∈ (fkRectTorusGraph R).edgeSet},
          if eta e then p else 1 - p := by
      apply Fintype.prod_equiv edgeEquiv
      intro e
      have heSet : e.1 ∈ (fkRectTorusGraph R).edgeSet :=
        SimpleGraph.mem_edgeFinset.mp e.2
      have hext : fkRectGraphConfigurationExtend R eta e.1 =
          eta (edgeEquiv e) := by
        unfold fkRectGraphConfigurationExtend
        rw [dif_pos heSet]
        congr 1
      rw [hext]


theorem fk_edgeProduct_configurationGraphEquiv
    (R : FKRectTorus) (p : Real) (omega : R.Configuration) :
    FK.edgeProduct (fkRectTorusGraph R) p
        (fkRectGraphConfigurationExtend R
          (fkRectConfigurationGraphEquiv R omega)) =
      fkRectEdgeProduct R p omega := by
  rw [fk_edgeProduct_configurationExtend]
  unfold fkRectEdgeProduct
  symm
  apply Fintype.prod_equiv (fkRectEdgeGraphEquiv R)
      (fun a => if omega a then p else 1 - p)
      (fun e => if fkRectConfigurationGraphEquiv R omega e then p else 1 - p)
  intro a
  rw [fkRectConfigurationGraphEquiv_apply_edge]


theorem fkWeight_configurationGraphEquiv
    (R : FKRectTorus) (p q : Real) (omega : R.Configuration) :
    FK.fkWeight (fkRectTorusGraph R) p q
        (fkRectGraphConfigurationExtend R
          (fkRectConfigurationGraphEquiv R omega)) =
      fkRectRandomClusterWeight R p q omega := by
  unfold FK.fkWeight fkRectRandomClusterWeight
  rw [fk_edgeProduct_configurationGraphEquiv,
    fk_numClusters_configurationExtend,
    fkRectGraph_clusterCount_configurationGraphEquiv]

@[simp] theorem fkRectGraphConfigurationExtend_sup
    (R : FKRectTorus) (eta zeta : FKRectGraphConfiguration R) :
    fkRectGraphConfigurationExtend R (eta ⊔ zeta) =
      fkRectGraphConfigurationExtend R eta ⊔
        fkRectGraphConfigurationExtend R zeta := by
  funext e
  by_cases he : e ∈ (fkRectTorusGraph R).edgeSet <;>
    simp [fkRectGraphConfigurationExtend, he]

@[simp] theorem fkRectGraphConfigurationExtend_inf
    (R : FKRectTorus) (eta zeta : FKRectGraphConfiguration R) :
    fkRectGraphConfigurationExtend R (eta ⊓ zeta) =
      fkRectGraphConfigurationExtend R eta ⊓
        fkRectGraphConfigurationExtend R zeta := by
  funext e
  by_cases he : e ∈ (fkRectTorusGraph R).edgeSet <;>
    simp [fkRectGraphConfigurationExtend, he]


end
end StatMech.FrontierD
