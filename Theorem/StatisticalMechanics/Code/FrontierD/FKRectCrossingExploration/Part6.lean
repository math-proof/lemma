/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCrossingExploration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalDualCrossings.Part7
import Theorem.StatisticalMechanics.Code.Probability.FiniteWitnessUnionBound
import Theorem.StatisticalMechanics.Code.FK.DomainMarkov.Part5
import Theorem.StatisticalMechanics.Code.FK.TwoPoint.Part4
import Theorem.StatisticalMechanics.Code.FK.OffCentreFreeDomination.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectCrossingExploration.Part6


namespace StatMech.FrontierD

noncomputable section

theorem fkRectPrimalInsertionArmEvent_isIncreasing
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (i : Fin R.height) (eta : R.Configuration) :
    IsIncreasing (FKRectPrimalInsertionArmEvent R S i eta) := by
  intro omega omega' hle
  rintro ⟨z, hreach⟩
  exact ⟨z, hreach.mono (FK.openSub_mono _ hle)⟩

theorem fkRectPrimalCrossing_insert_cluster_disjoint_explored_aux
    (R : FKRectTorus) (eta : R.Configuration)
    (S : Finset (Fin R.height)) (i : Fin R.height)
    (hi : i ∉ S)
    (hwitness : FKRectPrimalCrossingSourceWitnessCore R (insert i S) eta)
    {v : R.Vertex}
    (hiv : (fkRectOpenGraph R (fkRectForceCutClosed R eta)).Reachable
      (fkRectLeftColumn R, i) v) :
    ¬ FKRectPrimalExploredVertex R S eta v := by
  intro hexplored
  rcases hexplored with ⟨j, hj, hjv⟩
  have hri : i ∈ fkRectRawHorizontalCrossingRepresentativeIndices R
      (fkRectForceCutClosed R eta) :=
    hwitness (Finset.mem_insert_self i S)
  have hrj : j ∈ fkRectRawHorizontalCrossingRepresentativeIndices R
      (fkRectForceCutClosed R eta) :=
    hwitness (Finset.mem_insert_of_mem hj)
  have hcomponent := SimpleGraph.ConnectedComponent.sound
    (hiv.trans hjv.symm)
  have hij := eq_of_representativeIndices_of_component_eq R
    (fkRectForceCutClosed R eta) hri hrj hcomponent
  exact hi (hij ▸ hj)


theorem fkRectPrimalUnexploredGraph_adj_of_insert_reachable
    (R : FKRectTorus) (eta : R.Configuration)
    (S : Finset (Fin R.height)) (i : Fin R.height)
    (hi : i ∉ S)
    (hwitness : FKRectPrimalCrossingSourceWitnessCore R (insert i S) eta)
    {x y : R.Vertex}
    (hix : (fkRectOpenGraph R (fkRectForceCutClosed R eta)).Reachable
      (fkRectLeftColumn R, i) x)
    (hxy : (fkRectOpenGraph R (fkRectForceCutClosed R eta)).Adj x y) :
    (FK.openSub (fkRectPrimalUnexploredGraph R S eta)
      (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta))).Adj x y := by
  classical
  have hiy := hix.trans hxy.reachable
  have hxy_ne : x ≠ y := hxy.ne
  have hxNot := fkRectPrimalCrossing_insert_cluster_disjoint_explored_aux
    R eta S i hi hwitness hix
  have hyNot := fkRectPrimalCrossing_insert_cluster_disjoint_explored_aux
    R eta S i hi hwitness hiy
  rcases hxy with ⟨a, haopen, haedge⟩
  have haNotCut : a ∉ fkRectTorusCutEdges R := by
    intro hacut
    have := fkRectForceCutClosed_of_mem R eta a hacut
    rw [haopen] at this
    exact Bool.noConfusion this
  have hedgeNotCut : s(x, y) ∉ fkRectTorusCutGraphEdges R := by
    rw [← haedge, mem_fkRectTorusCutGraphEdges]
    exact haNotCut
  have hnotTouch : ¬ ∃ v w : R.Vertex, s(x, y) = s(v, w) ∧
      (FKRectPrimalExploredVertex R S eta v ∨
        FKRectPrimalExploredVertex R S eta w) := by
    rintro ⟨v, w, hvw, hv | hw⟩
    · rcases Sym2.eq_iff.mp hvw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hxNot hv
      · exact hyNot hv
    · rcases Sym2.eq_iff.mp hvw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hyNot hw
      · exact hxNot hw
  constructor
  · rw [fkRectPrimalUnexploredGraph, SimpleGraph.fromEdgeSet_adj]
    have htorusAdj : (fkRectTorusGraph R).Adj x y :=
      (SimpleGraph.mem_edgeSet (fkRectTorusGraph R)).1
        ((mem_fkRectTorusGraph_edgeSet_iff R _).2 ⟨a, haedge⟩)
    exact ⟨Finset.mem_coe.mpr (Finset.mem_filter.mpr
      ⟨SimpleGraph.mem_edgeFinset.mpr htorusAdj,
        hedgeNotCut, hnotTouch⟩), hxy_ne⟩
  · rw [← haedge, fkRectFullGraphConfiguration_indexedEdge]
    exact haopen


theorem fkRectPrimalUnexplored_reachable_of_insert_reachable
    (R : FKRectTorus) (eta : R.Configuration)
    (S : Finset (Fin R.height)) (i : Fin R.height)
    (hi : i ∉ S)
    (hwitness : FKRectPrimalCrossingSourceWitnessCore R (insert i S) eta)
    {v : R.Vertex}
    (hiv : (fkRectOpenGraph R (fkRectForceCutClosed R eta)).Reachable
      (fkRectLeftColumn R, i) v) :
    (FK.openSub (fkRectPrimalUnexploredGraph R S eta)
      (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta))).Reachable
        (fkRectLeftColumn R, i) v := by
  let source : R.Vertex := (fkRectLeftColumn R, i)
  let G := fkRectOpenGraph R (fkRectForceCutClosed R eta)
  let H := FK.openSub (fkRectPrimalUnexploredGraph R S eta)
    (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta))
  let liftWalk : ∀ {x y : R.Vertex}, G.Walk x y →
      G.Reachable source x → H.Walk x y := by
    intro x y p
    induction p with
    | nil => intro _; exact SimpleGraph.Walk.nil
    | @cons x y z hxy p ih =>
        intro hsx
        exact SimpleGraph.Walk.cons
          (fkRectPrimalUnexploredGraph_adj_of_insert_reachable
            R eta S i hi hwitness hsx hxy)
          (ih (hsx.trans hxy.reachable))
  exact hiv.elim fun p =>
    ⟨liftWalk p (SimpleGraph.Reachable.refl source)⟩


theorem fkRectPrimalCrossingSourceWitnessCore_insert_imp_arm
    (R : FKRectTorus) (eta : R.Configuration)
    (S : Finset (Fin R.height)) (i : Fin R.height)
    (hi : i ∉ S)
    (hwitness : FKRectPrimalCrossingSourceWitnessCore R (insert i S) eta) :
    fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta) ∈
      FKRectPrimalInsertionArmEvent R S i eta := by
  have hrep : i ∈ fkRectRawHorizontalCrossingRepresentativeIndices R
      (fkRectForceCutClosed R eta) :=
    hwitness (Finset.mem_insert_self i S)
  obtain ⟨z, hiz⟩ :=
    fkRectRawHorizontalCrossingRepresentativeIndices_subset_sources
      R (fkRectForceCutClosed R eta) i hrep
  exact ⟨z, fkRectPrimalUnexplored_reachable_of_insert_reachable
    R eta S i hi hwitness hiz⟩


theorem fkRectPrimalCrossing_insert_cluster_disjoint_explored
    (R : FKRectTorus) (eta : R.Configuration)
    (S : Finset (Fin R.height)) (i : Fin R.height)
    (hi : i ∉ S)
    (hwitness : FKRectPrimalCrossingSourceWitnessCore R (insert i S) eta)
    {v : R.Vertex}
    (hiv : (fkRectOpenGraph R (fkRectForceCutClosed R eta)).Reachable
      (fkRectLeftColumn R, i) v) :
    ¬ FKRectPrimalExploredVertex R S eta v := by
  intro hexplored
  rcases hexplored with ⟨j, hj, hjv⟩
  have hri : i ∈ fkRectRawHorizontalCrossingRepresentativeIndices R
      (fkRectForceCutClosed R eta) :=
    hwitness (Finset.mem_insert_self i S)
  have hrj : j ∈ fkRectRawHorizontalCrossingRepresentativeIndices R
      (fkRectForceCutClosed R eta) :=
    hwitness (Finset.mem_insert_of_mem hj)
  have hcomponent := SimpleGraph.ConnectedComponent.sound
    (hiv.trans hjv.symm)
  have hij := eq_of_representativeIndices_of_component_eq R
    (fkRectForceCutClosed R eta) hri hrj hcomponent
  exact hi (hij ▸ hj)


theorem fkRectPrimalCrossing_insert_source_not_explored
    (R : FKRectTorus) (eta : R.Configuration)
    (S : Finset (Fin R.height)) (i : Fin R.height)
    (hi : i ∉ S)
    (hwitness : FKRectPrimalCrossingSourceWitnessCore R (insert i S) eta) :
    ¬ FKRectPrimalExploredVertex R S eta (fkRectLeftColumn R, i) := by
  apply fkRectPrimalCrossing_insert_cluster_disjoint_explored
    R eta S i hi hwitness
  exact SimpleGraph.Reachable.refl (fkRectLeftColumn R, i)


end
end StatMech.FrontierD
