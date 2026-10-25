/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredDoubleVisitPortGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part34
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredOpenFibers
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredDoubleVisitPortGeometry.Part3


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareWired_exhaustiveSwitchingLaw
    (n : Nat) (hn : 0 < n)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    (fkIsingSquareWiredDobrushinDomain n hn).ExhaustiveExplorationSwitchingLaw := by
  let D := fkIsingSquareWiredDobrushinDomain n hn
  refine {
    crossingEdge := e.1
    edges := fkIsingSquareWiredLocalCarrierDarts n e
    caseAt := ?_ }
  intro omega
  apply Classical.choice
  rcases fkIsingSquareWired_local_switch_component_classification
      n hn omega e with hzero | hwest | heast | hdouble
  · rcases hzero with ⟨hWTrace, hETrace, hopenTrace⟩
    have hW : ¬fkIsingSquareWiredPathUsesLocalSide n hn
        (setClosed e.1 omega) e .west := by
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hWTrace
    have hE : ¬fkIsingSquareWiredPathUsesLocalSide n hn
        (setClosed e.1 omega) e .east := by
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hETrace
    have hS : ¬fkIsingSquareWiredPathUsesLocalSide n hn
        (setClosed e.1 omega) e .south := by
      intro hS
      apply hW
      have hSmem : (.dart (e, .south) : FKIsingSquareWiredCarrier n) ∈
          (fkIsingSquareWiredDobrushinDomain n hn).exploration
            (setClosed e.1 omega) := by
        rw [mem_fkIsingSquareWiredDobrushinDomain_exploration_iff_order]
        exact hS
      have hWmem := (fkIsingSquareWired_closed_west_mem_iff_south
        n hn omega e).2 hSmem
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hWmem
    have hN : ¬fkIsingSquareWiredPathUsesLocalSide n hn
        (setClosed e.1 omega) e .north := by
      intro hN
      apply hE
      have hNmem : (.dart (e, .north) : FKIsingSquareWiredCarrier n) ∈
          (fkIsingSquareWiredDobrushinDomain n hn).exploration
            (setClosed e.1 omega) := by
        rw [mem_fkIsingSquareWiredDobrushinDomain_exploration_iff_order]
        exact hN
      have hEmem := (fkIsingSquareWired_closed_east_mem_iff_north
        n hn omega e).2 hNmem
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hEmem
    have hopen (side) : ¬fkIsingSquareWiredPathUsesLocalSide n hn
        (setOpen e.1 omega) e side := by
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hopenTrace side
    refine ⟨FKIsingDobrushinDomain.PointwiseExplorationSwitchingCase.caseOne ?_ ?_⟩
    · intro k
      rw [mem_fkIsingSquareWiredDobrushinDomain_exploration_iff_order]
      fin_cases k
      · exact hW
      · exact hE
      · exact hS
      · exact hN
    · intro k
      rw [mem_fkIsingSquareWiredDobrushinDomain_exploration_iff_order]
      fin_cases k
      · exact hopen .west
      · exact hopen .east
      · exact hopen .south
      · exact hopen .north
  · rcases hwest with ⟨hWTrace, hETrace, hopenTrace⟩
    have hW : fkIsingSquareWiredPathUsesLocalSide n hn
        (setClosed e.1 omega) e .west := by
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hWTrace
    have hE : ¬fkIsingSquareWiredPathUsesLocalSide n hn
        (setClosed e.1 omega) e .east := by
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hETrace
    have hopen (side) : fkIsingSquareWiredPathUsesLocalSide n hn
        (setOpen e.1 omega) e side := by
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hopenTrace side
    exact ⟨FKIsingDobrushinDomain.PointwiseExplorationSwitchingCase.caseTwo
      (fkIsingSquareWired_one_visit_west_contour_balance
      n hn omega e hW hE hopen
        (fkIsingSquareWired_one_visit_west_phase n hn omega e hW hE)
        (fkIsingSquareWired_one_visit_west_inserted_phase
          n hn omega e hW hE))⟩
  · rcases heast with ⟨hWTrace, hETrace, hopenTrace⟩
    have hW : ¬fkIsingSquareWiredPathUsesLocalSide n hn
        (setClosed e.1 omega) e .west := by
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hWTrace
    have hE : fkIsingSquareWiredPathUsesLocalSide n hn
        (setClosed e.1 omega) e .east := by
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hETrace
    have hopen (side) : fkIsingSquareWiredPathUsesLocalSide n hn
        (setOpen e.1 omega) e side := by
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hopenTrace side
    exact ⟨FKIsingDobrushinDomain.PointwiseExplorationSwitchingCase.caseTwo
      (fkIsingSquareWired_one_visit_east_contour_balance
      n hn omega e hW hE hopen
        (fkIsingSquareWired_one_visit_east_phase n hn omega e hW hE)
        (fkIsingSquareWired_one_visit_east_inserted_phase
          n hn omega e hW hE))⟩
  · rcases hdouble with ⟨hWTrace, hETrace⟩
    have hW : fkIsingSquareWiredPathUsesLocalSide n hn
        (setClosed e.1 omega) e .west := by
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hWTrace
    have hE : fkIsingSquareWiredPathUsesLocalSide n hn
        (setClosed e.1 omega) e .east := by
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hETrace
    exact ⟨FKIsingDobrushinDomain.PointwiseExplorationSwitchingCase.caseThree
      (fkIsingSquareWired_double_visit_pointwise_contour_balance
        n hn omega e hW hE)⟩


end
end StatMech.Universality
