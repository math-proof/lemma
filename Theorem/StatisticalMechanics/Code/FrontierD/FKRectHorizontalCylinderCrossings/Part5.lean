/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderCrossings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderLaw.Part5
import Def.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderCrossings.Part5
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem exists_fkRectHorizontalCylinderDistinctPairedWitness
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex)) (n : Nat)
    (hn : n <= fkRectHorizontalCylinderCrossingClusterCount R rho) :
    ∃ S : Finset (Fin R.width), S.card = n ∧
      FKRectHorizontalCylinderDistinctPairedWitness R
        (fkRectHorizontalCylinderCrossingTarget R rho) S rho := by
  classical
  let available :=
    fkRectHorizontalCylinderCrossingRepresentativeIndices R rho
  have hnAvailable : n <= available.card := by
    rw [card_fkRectHorizontalCylinderCrossingRepresentativeIndices]
    exact hn
  obtain ⟨S, hsub, hcard⟩ :=
    Finset.exists_subset_card_eq hnAvailable
  refine ⟨S, hcard, ?_, ?_⟩
  · intro x hx
    exact fkRectHorizontalCylinderCrossingTarget_reachable R rho
      (fkRectHorizontalCylinderCrossingRepresentativeIndices_subset_sources
        R rho x (hsub hx))
  · intro x hx y hy hxy hreach
    apply hxy
    apply eq_of_horizontalCylinder_representatives_of_component_eq
      R rho (hsub hx) (hsub hy)
    exact SimpleGraph.ConnectedComponent.sound hreach


theorem fkRectHorizontalCylinderCrossingTail_le_choose_mul_pairCount_mul
    (R : FKRectTorus)
    (mu : ConfigSpace (Sym2 R.Vertex) -> Real)
    (hmu : ∀ rho, 0 <= mu rho) (n : Nat) (a : Real)
    (hmass : ∀ S : Finset (Fin R.width), S.card = n ->
      ∀ pair : Fin R.width -> Fin R.width,
        StatMech.Probability.finiteEventMass mu
          {rho | FKRectHorizontalCylinderDistinctPairedWitness
            R pair S rho} <= a) :
    StatMech.Probability.finiteEventMass mu
        {rho | n <= fkRectHorizontalCylinderCrossingClusterCount R rho} <=
      Nat.choose R.width n * R.width ^ R.width * a := by
  classical
  let subsets : Finset (Finset (Fin R.width)) :=
    (Finset.univ : Finset (Fin R.width)).powersetCard n
  let Pair := Fin R.width -> Fin R.width
  have hpoint (rho : ConfigSpace (Sym2 R.Vertex)) :
      (if n <= fkRectHorizontalCylinderCrossingClusterCount R rho then
          mu rho else 0) <=
        subsets.sum (fun S =>
          (Finset.univ : Finset Pair).sum (fun pair =>
            if FKRectHorizontalCylinderDistinctPairedWitness
                R pair S rho then mu rho else 0)) := by
    by_cases htail : n <=
        fkRectHorizontalCylinderCrossingClusterCount R rho
    · rw [if_pos htail]
      obtain ⟨S, hcard, hW⟩ :=
        exists_fkRectHorizontalCylinderDistinctPairedWitness
          R rho n htail
      let pair := fkRectHorizontalCylinderCrossingTarget R rho
      have hS : S ∈ subsets := by
        simp [subsets, hcard]
      have hpair : pair ∈ (Finset.univ : Finset Pair) :=
        Finset.mem_univ pair
      have hinner : mu rho <=
          (Finset.univ : Finset Pair).sum (fun target =>
            if FKRectHorizontalCylinderDistinctPairedWitness
                R target S rho then mu rho else 0) := by
        have hsingle := Finset.single_le_sum
          (s := (Finset.univ : Finset Pair))
          (f := fun target =>
            if FKRectHorizontalCylinderDistinctPairedWitness
                R target S rho then mu rho else 0)
          (fun target _ => by
            by_cases htarget :
                FKRectHorizontalCylinderDistinctPairedWitness
                  R target S rho <;>
              simp [htarget, hmu rho]) hpair
        simpa [pair, hW] using hsingle
      exact hinner.trans (Finset.single_le_sum
        (s := subsets)
        (f := fun T =>
          (Finset.univ : Finset Pair).sum (fun target =>
            if FKRectHorizontalCylinderDistinctPairedWitness
                R target T rho then mu rho else 0))
        (fun T _ => Finset.sum_nonneg fun target _ => by
          by_cases htarget :
              FKRectHorizontalCylinderDistinctPairedWitness
                R target T rho <;>
            simp [htarget, hmu rho]) hS)
    · rw [if_neg htail]
      exact Finset.sum_nonneg fun S _ =>
        Finset.sum_nonneg fun pair _ => by
          by_cases hpair :
              FKRectHorizontalCylinderDistinctPairedWitness
                R pair S rho <;>
            simp [hpair, hmu rho]
  calc
    StatMech.Probability.finiteEventMass mu
        {rho | n <= fkRectHorizontalCylinderCrossingClusterCount R rho} =
      ∑ rho, if n <=
          fkRectHorizontalCylinderCrossingClusterCount R rho then
        mu rho else 0 := by
          unfold StatMech.Probability.finiteEventMass
          apply Finset.sum_congr rfl
          intro rho _
          simp
    _ <= ∑ rho, subsets.sum (fun S =>
        (Finset.univ : Finset Pair).sum (fun pair =>
          if FKRectHorizontalCylinderDistinctPairedWitness
              R pair S rho then mu rho else 0)) :=
      Finset.sum_le_sum fun rho _ => hpoint rho
    _ = subsets.sum (fun S =>
        (Finset.univ : Finset Pair).sum (fun pair =>
          StatMech.Probability.finiteEventMass mu
            {rho | FKRectHorizontalCylinderDistinctPairedWitness
              R pair S rho})) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro S _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro pair _
      unfold StatMech.Probability.finiteEventMass
      apply Finset.sum_congr rfl
      intro rho _
      rfl
    _ <= subsets.sum (fun _ =>
        (Finset.univ : Finset Pair).sum (fun _ => a)) := by
      apply Finset.sum_le_sum
      intro S hS
      have hcard : S.card = n := by
        simpa [subsets] using hS
      exact Finset.sum_le_sum fun pair _ => hmass S hcard pair
    _ = Nat.choose R.width n * R.width ^ R.width * a := by
      simp [subsets, Pair, Finset.card_powersetCard]
      ring

theorem fkRectHorizontalCutClosedConfiguration_force_eq_self
    (R : FKRectTorus) (eta : R.Configuration)
    (hclosed : FKRectHorizontalCutClosedConfiguration R eta) :
    fkRectForceHorizontalCutClosed R eta = eta := by
  funext a
  by_cases ha : a ∈ fkRectHorizontalCutEdges R
  · simp [fkRectForceHorizontalCutClosed, fkRectForceEdgesClosed,
      ha, hclosed a ha]
  · simp [fkRectForceHorizontalCutClosed, fkRectForceEdgesClosed, ha]


theorem openSub_ecz_closeOff_horizontalCylinder
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex)) :
    FK.openSub (fkRectHorizontalCylinderGraph R)
        (FK.ecz_closeOff (fkRectHorizontalCylinderGraph R) rho).1 =
      FK.openSub (fkRectHorizontalCylinderGraph R) rho := by
  apply SimpleGraph.ext
  ext x y
  simp only [FK.openSub_adj]
  constructor
  · rintro ⟨hxy, hopen⟩
    exact ⟨hxy, by
      have hedge : s(x, y) ∈
          (fkRectHorizontalCylinderGraph R).edgeFinset := by
        rw [SimpleGraph.mem_edgeFinset]
        exact hxy
      simpa using (FK.ecz_closeOff_apply_edge
        (fkRectHorizontalCylinderGraph R) rho hedge).symm.trans hopen⟩
  · rintro ⟨hxy, hopen⟩
    refine ⟨hxy, ?_⟩
    have hedge : s(x, y) ∈
        (fkRectHorizontalCylinderGraph R).edgeFinset := by
      rw [SimpleGraph.mem_edgeFinset]
      exact hxy
    simpa using (FK.ecz_closeOff_apply_edge
      (fkRectHorizontalCylinderGraph R) rho hedge).trans hopen

theorem FKRectHorizontalCylinderDistinctPairedWitness.congr_openSub
    (R : FKRectTorus) (pair : Fin R.width -> Fin R.width)
    (S : Finset (Fin R.width))
    {rho sigma : ConfigSpace (Sym2 R.Vertex)}
    (hgraph : FK.openSub (fkRectHorizontalCylinderGraph R) rho =
      FK.openSub (fkRectHorizontalCylinderGraph R) sigma) :
    FKRectHorizontalCylinderDistinctPairedWitness R pair S rho ↔
      FKRectHorizontalCylinderDistinctPairedWitness R pair S sigma := by
  unfold FKRectHorizontalCylinderDistinctPairedWitness
  rw [hgraph]


end
end StatMech.FrontierD
