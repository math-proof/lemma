/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectAugmentedBarrierWindingMass.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectAugmentedSourceBarrier.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectAugmentedBarrierWindingMass
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectFullGraphEvent_to_indexed
    (R : FKRectTorus) (B : Set R.Configuration)
    {rho : ConfigSpace (Sym2 R.Vertex)}
    (hrho : rho ∈ fkRectFullGraphEvent R B) :
    fkRectIndexedConfigurationOfFullGraph R rho ∈ B :=
  hrho


theorem fkRectInduced_openSub_indexedConfiguration_eq
    (R : FKRectTorus) (S : Set R.Vertex)
    (rho : ConfigSpace (Sym2 R.Vertex)) :
    FK.openSub (fkRectInducedGraph R S)
        (FK.ocd_innerRestrict
          (Subtype.val : FKRectInducedVertex R S → R.Vertex)
          (fkRectFullGraphConfiguration R
            (fkRectIndexedConfigurationOfFullGraph R rho))) =
      FK.openSub (fkRectInducedGraph R S)
        (FK.ocd_innerRestrict
          (Subtype.val : FKRectInducedVertex R S → R.Vertex) rho) := by
  let sigma := FK.ecz_closeOff (fkRectTorusGraph R) rho
  let omega := fkRectIndexedConfigurationOfFullGraph R rho
  have hsigma : fkRectFullEdgeConfigEquiv R omega = sigma := by
    exact (fkRectFullEdgeConfigEquiv R).apply_symm_apply sigma
  have hfull : fkRectFullGraphConfiguration R omega = sigma.1 :=
    congrArg Subtype.val hsigma
  ext u v
  constructor
  · rintro ⟨hadj, hopen⟩
    refine ⟨hadj, ?_⟩
    have hedge : s(u.1, v.1) ∈ (fkRectTorusGraph R).edgeFinset := by
      rw [SimpleGraph.mem_edgeFinset]
      exact hadj
    change fkRectFullGraphConfiguration R omega s(u.1, v.1) = true at hopen
    change rho s(u.1, v.1) = true
    rw [hfull, FK.ecz_closeOff_apply_edge _ _ hedge] at hopen
    exact hopen
  · rintro ⟨hadj, hopen⟩
    refine ⟨hadj, ?_⟩
    have hedge : s(u.1, v.1) ∈ (fkRectTorusGraph R).edgeFinset := by
      rw [SimpleGraph.mem_edgeFinset]
      exact hadj
    change rho s(u.1, v.1) = true at hopen
    change fkRectFullGraphConfiguration R omega s(u.1, v.1) = true
    rw [hfull, FK.ecz_closeOff_apply_edge _ _ hedge]
    exact hopen

theorem fkRectInduced_connectionChain_to_indexedConfiguration
    (R : FKRectTorus) (S : Set R.Vertex)
    (rho : ConfigSpace (Sym2 R.Vertex))
    (t : Finset (FKRectInducedVertex R S × FKRectInducedVertex R S))
    (hchain :
      FK.ocd_innerRestrict
          (Subtype.val : FKRectInducedVertex R S → R.Vertex) rho ∈
        fkRectInducedConnectionChainEvent R S t) :
    FK.ocd_innerRestrict
        (Subtype.val : FKRectInducedVertex R S → R.Vertex)
        (fkRectFullGraphConfiguration R
          (fkRectIndexedConfigurationOfFullGraph R rho)) ∈
      fkRectInducedConnectionChainEvent R S t := by
  intro p hp
  have hreach := hchain p hp
  change (FK.openSub (fkRectInducedGraph R S)
    (FK.ocd_innerRestrict
      (Subtype.val : FKRectInducedVertex R S → R.Vertex)
      (fkRectFullGraphConfiguration R
        (fkRectIndexedConfigurationOfFullGraph R rho)))).Reachable p.1 p.2
  change (FK.openSub (fkRectInducedGraph R S)
    (FK.ocd_innerRestrict
      (Subtype.val : FKRectInducedVertex R S → R.Vertex) rho)).Reachable
        p.1 p.2 at hreach
  rw [fkRectInduced_openSub_indexedConfiguration_eq R S rho]
  exact hreach


theorem fkRectAugmentedBarrierConnectionEvent_subset_fullGraphVerticalWinding
    (R : FKRectTorus) (leftRight cut : Nat)
    {gap : R.EdgeIndex} (hgap : gap ∈ fkRectHorizontalCutEdges R)
    (x : Fin R.width) (hx : cut ≤ x.val)
    (hchosen : fkRectVerticalSeamEdgeAt R x ≠ gap)
    (t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) ×
      FKRectRightStripBandVertex R cut 1 (R.height - 1)))
    (hpair : (fkRectRightBandRowOne R cut x hx,
      fkRectRightBandLastRow R cut x hx) ∈ t) :
    fkRectAugmentedBarrierConnectionEvent R
        leftRight cut gap x t ⊆
      fkRectFullGraphEvent R (fkRectVerticalWindingEvent R) := by
  intro rho hrho
  let omega := fkRectIndexedConfigurationOfFullGraph R rho
  have hbarrier : omega ∈
      fkRectAugmentedSourceBarrier R leftRight gap x :=
    fkRectFullGraphEvent_to_indexed R _ hrho.2
  have hchain :
      FK.ocd_innerRestrict
          (Subtype.val :
            FKRectRightStripBandVertex R cut 1 (R.height - 1) → R.Vertex)
          (fkRectFullGraphConfiguration R omega) ∈
        fkRectInducedConnectionChainEvent R
          (fkRectRightStripBand R cut 1 (R.height - 1)) t := by
    exact fkRectInduced_connectionChain_to_indexedConfiguration R
      (fkRectRightStripBand R cut 1 (R.height - 1)) rho t hrho.1
  have hopen := fkRectAugmentedSourceBarrier_witnessEdges_open
    R leftRight hgap x hchosen hbarrier
  change omega ∈ fkRectVerticalWindingEvent R
  exact fkRectVerticalWindingEvent_of_rightBand_chain
    R cut x hx omega t hpair hchain hopen.1 hopen.2


end
end StatMech.FrontierD
