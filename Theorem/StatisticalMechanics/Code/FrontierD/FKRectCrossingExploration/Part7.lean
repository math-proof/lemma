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
import Instance.StatisticalMechanics.Code.FrontierD.FKRectCrossingExploration.Part7


namespace StatMech.FrontierD

noncomputable section

theorem fkRectPrimalExploredVertex_of_openAdj_right
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) {x y : R.Vertex}
    (hxy : (fkRectOpenGraph R (fkRectForceCutClosed R eta)).Adj x y)
    (hy : FKRectPrimalExploredVertex R S eta y) :
    FKRectPrimalExploredVertex R S eta x := by
  rcases hy with ⟨i, hi, hiy⟩
  exact ⟨i, hi, hiy.trans hxy.symm.reachable⟩


theorem not_primalExplorationOutsideOpenGraph_adj_of_not_explored
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) {x y : R.Vertex}
    (hx : ¬ FKRectPrimalExploredVertex R S eta x) :
    ¬ (fkRectPrimalExplorationOutsideOpenGraph R S eta).Adj x y := by
  classical
  rintro ⟨hxy, hopen, hout⟩
  have hOpenAdj :
      (fkRectOpenGraph R (fkRectForceCutClosed R eta)).Adj x y := by
    obtain ⟨a, ha⟩ :=
      (mem_fkRectTorusGraph_edgeSet_iff R s(x, y)).1
        ((SimpleGraph.mem_edgeSet (fkRectTorusGraph R)).2 hxy)
    refine ⟨a, ?_, ha⟩
    rw [← fkRectFullGraphConfiguration_indexedEdge R
      (fkRectForceCutClosed R eta) a, ha]
    exact hopen
  have htouch : ∃ v w : R.Vertex, s(x, y) = s(v, w) ∧
      (FKRectPrimalExploredVertex R S eta v ∨
        FKRectPrimalExploredVertex R S eta w) := by
    by_contra hnot
    have hnotCut : s(x, y) ∉ fkRectTorusCutGraphEdges R := by
      intro hcut
      have hfalse :=
        fkRectFullGraphConfiguration_forceCut_eq_false_of_cutEdge
          R eta hcut
      rw [hopen] at hfalse
      exact Bool.noConfusion hfalse
    exact hout (Finset.mem_filter.mpr
      ⟨SimpleGraph.mem_edgeFinset.mpr hxy, hnotCut, hnot⟩)
  rcases htouch with ⟨v, w, hvw, hv | hw⟩
  · rcases Sym2.eq_iff.mp hvw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hx hv
    · exact hx (fkRectPrimalExploredVertex_of_openAdj_right
        R S eta hOpenAdj hv)
  · rcases Sym2.eq_iff.mp hvw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hx (fkRectPrimalExploredVertex_of_openAdj_right
        R S eta hOpenAdj hw)
    · exact hx hw


theorem not_primalExplorationInducedBoundary_adj_of_not_explored
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) {x y : R.Vertex}
    (hx : ¬ FKRectPrimalExploredVertex R S eta x)
    (hy : ¬ FKRectPrimalExploredVertex R S eta y) :
    ¬ (fkRectPrimalExplorationInducedBoundary R S eta).Adj x y := by
  rintro ⟨hxy, hreach⟩
  apply hxy
  exact hreach.elim fun p => by
    have hpzero : p.length = 0 := by
      cases p with
      | nil => rfl
      | cons hadj rest =>
          exact False.elim
            (not_primalExplorationOutsideOpenGraph_adj_of_not_explored
              R S eta hx hadj)
    exact p.eq_of_length_eq_zero hpzero


end
end StatMech.FrontierD
