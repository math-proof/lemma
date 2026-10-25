/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareExhaustive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquarePrimalConnectivity.Part2
import Structure.StatisticalMechanics.Code.Universality.IsingFermionicSquareExhaustive


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC
  StatMech.FrontierD

noncomputable section

def fkIsingSquare_exhaustiveSwitchingLaw
    (n : Nat) (hn : 0 < n)
    (geometry : FKIsingSquareSwitchingGeometry n hn)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    (fkIsingSquareDobrushinDomain n hn).ExhaustiveExplorationSwitchingLaw := by
  let D := fkIsingSquareDobrushinDomain n hn
  refine {
    crossingEdge := e.1
    edges := fkIsingSquareLocalCarrierDarts n e
    caseAt := ?_ }
  intro omega
  apply Classical.choice
  rcases fkIsingSquare_local_switch_path_membership_classification
      n hn omega e with hzero | hwest | heast | hdouble
  · rcases hzero with ⟨hW, hE, hopen⟩
    have hS : ¬ fkIsingSquarePathUsesLocalSide n hn
        (setClosed e.1 omega) e .south := by
      intro h
      exact hW ((fkIsingSquare_closed_pathUses_west_iff_south
        n hn omega e).2 h)
    have hN : ¬ fkIsingSquarePathUsesLocalSide n hn
        (setClosed e.1 omega) e .north := by
      intro h
      exact hE ((fkIsingSquare_closed_pathUses_east_iff_north
        n hn omega e).2 h)
    refine ⟨FKIsingDobrushinDomain.PointwiseExplorationSwitchingCase.caseOne ?_ ?_⟩
    · intro k
      fin_cases k
      · simpa only [D, fkIsingSquareLocalCarrierDarts,
          fkIsingSquareDobrushinDomain, fkIsingSquarePathUsesLocalSide] using hW
      · simpa only [D, fkIsingSquareLocalCarrierDarts,
          fkIsingSquareDobrushinDomain, fkIsingSquarePathUsesLocalSide] using hE
      · simpa only [D, fkIsingSquareLocalCarrierDarts,
          fkIsingSquareDobrushinDomain, fkIsingSquarePathUsesLocalSide] using hS
      · simpa only [D, fkIsingSquareLocalCarrierDarts,
          fkIsingSquareDobrushinDomain, fkIsingSquarePathUsesLocalSide] using hN
    · intro k
      fin_cases k
      · simpa only [D, fkIsingSquareLocalCarrierDarts,
          fkIsingSquareDobrushinDomain, fkIsingSquarePathUsesLocalSide] using hopen .west
      · simpa only [D, fkIsingSquareLocalCarrierDarts,
          fkIsingSquareDobrushinDomain, fkIsingSquarePathUsesLocalSide] using hopen .east
      · simpa only [D, fkIsingSquareLocalCarrierDarts,
          fkIsingSquareDobrushinDomain, fkIsingSquarePathUsesLocalSide] using hopen .south
      · simpa only [D, fkIsingSquareLocalCarrierDarts,
          fkIsingSquareDobrushinDomain, fkIsingSquarePathUsesLocalSide] using hopen .north
  · rcases hwest with ⟨hW, hE, hopen⟩
    have hsepGadget := geometry.oneVisitSeparated omega e (Or.inl ⟨hW, hE⟩)
    have hsep : ¬
        (openSub (fkSquareBoxPlanar n).G (setClosed e.1 omega) ⊔
          (fkIsingSquareDobrushinDomain n hn).wiring).Reachable
            (fkIsingSquareOrientedEdge n e).tail
            (fkIsingSquareOrientedEdge n e).head := by
      rw [FKIsingDobrushinDomain.wiring]
      exact fun h => hsepGadget
        ((fkIsingSquare_openWiredExteriorGadget_reachable_iff n
          (setClosed e.1 omega) _ _).2 h)
    obtain ⟨hphaseW, hphaseS⟩ := geometry.oneVisitWestPhase omega e hW hE
    exact ⟨FKIsingDobrushinDomain.PointwiseExplorationSwitchingCase.caseTwo
      (fkIsingSquare_one_visit_west_pointwise_contour_balance
        n hn omega e hW hE hopen hsep hphaseW hphaseS)⟩
  · rcases heast with ⟨hW, hE, hopen⟩
    have hsepGadget := geometry.oneVisitSeparated omega e (Or.inr ⟨hW, hE⟩)
    have hsep : ¬
        (openSub (fkSquareBoxPlanar n).G (setClosed e.1 omega) ⊔
          (fkIsingSquareDobrushinDomain n hn).wiring).Reachable
            (fkIsingSquareOrientedEdge n e).tail
            (fkIsingSquareOrientedEdge n e).head := by
      rw [FKIsingDobrushinDomain.wiring]
      exact fun h => hsepGadget
        ((fkIsingSquare_openWiredExteriorGadget_reachable_iff n
          (setClosed e.1 omega) _ _).2 h)
    obtain ⟨hphaseE, hphaseN⟩ := geometry.oneVisitEastPhase omega e hW hE
    exact ⟨FKIsingDobrushinDomain.PointwiseExplorationSwitchingCase.caseTwo
      (fkIsingSquare_one_visit_east_pointwise_contour_balance
        n hn omega e hW hE hopen hsep hphaseE hphaseN)⟩
  · rcases hdouble with ⟨hW, hE⟩
    exact ⟨FKIsingDobrushinDomain.PointwiseExplorationSwitchingCase.caseThree
      (fkIsingSquare_double_visit_pointwise_contour_balance_of_discardedLoopTurn
        n hn omega e hW hE
          (geometry.doubleVisitLoopTurn omega e hW hE))⟩


end
end StatMech.Universality
