/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayer.Part8
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerSwitching


namespace StatMech.Universality

open Finset Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareBoundary_exhaustiveSwitchingLaw
    (n : Nat) (hn : 0 < n)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (he : e.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n) :
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).ExhaustiveExplorationSwitchingLaw := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  refine {
    crossingEdge := e.1
    edges := fkIsingSquareWiredLocalCarrierDarts n e
    caseAt := ?_ }
  intro omega
  let omega' := fkIsingSquareClosePerimeter n omega
  apply Classical.choice
  rcases fkIsingSquareWired_local_switch_component_classification
      n hn omega' e with hzero | hwest | heast | hdouble
  · rcases hzero with ⟨hWTrace, hETrace, hopenTrace⟩
    have hW : ¬fkIsingSquareWiredPathUsesLocalSide n hn
        (setClosed e.1 omega') e .west := by
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hWTrace
    have hE : ¬fkIsingSquareWiredPathUsesLocalSide n hn
        (setClosed e.1 omega') e .east := by
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hETrace
    have hS : ¬fkIsingSquareWiredPathUsesLocalSide n hn
        (setClosed e.1 omega') e .south := by
      intro hS
      apply hW
      rw [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace]
      apply (fkIsingSquareWired_closed_west_mem_iff_south n hn omega' e).2
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hS
    have hN : ¬fkIsingSquareWiredPathUsesLocalSide n hn
        (setClosed e.1 omega') e .north := by
      intro hN
      apply hE
      rw [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace]
      apply (fkIsingSquareWired_closed_east_mem_iff_north n hn omega' e).2
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hN
    have hopen (side) : ¬fkIsingSquareWiredPathUsesLocalSide n hn
        (setOpen e.1 omega') e side := by
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hopenTrace side
    have hclosedSide (side : FKIsingMedialSide)
        (h : ¬fkIsingSquareWiredPathUsesLocalSide n hn
          (setClosed e.1 omega') e side) :
        (.dart (e, side) : FKIsingSquareWiredCarrier n) ∉
          D.exploration (setClosed e.1 omega) := by
      change (.dart (e, side) : FKIsingSquareWiredCarrier n) ∉
        fkIsingSquareWiredExplorationOrder n hn
          (fkIsingSquareClosePerimeter n (setClosed e.1 omega))
      rw [fkIsingSquareClosePerimeter_setClosed]
      simpa only [omega', fkIsingSquareWiredPathUsesLocalSide] using h
    have hopenSide (side : FKIsingMedialSide)
        (h : ¬fkIsingSquareWiredPathUsesLocalSide n hn
          (setOpen e.1 omega') e side) :
        (.dart (e, side) : FKIsingSquareWiredCarrier n) ∉
          D.exploration (setOpen e.1 omega) := by
      change (.dart (e, side) : FKIsingSquareWiredCarrier n) ∉
        fkIsingSquareWiredExplorationOrder n hn
          (fkIsingSquareClosePerimeter n (setOpen e.1 omega))
      rw [fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he]
      simpa only [omega', fkIsingSquareWiredPathUsesLocalSide] using h
    refine ⟨FKIsingDobrushinDomain.PointwiseExplorationSwitchingCase.caseOne ?_ ?_⟩
    · intro k
      fin_cases k
      · exact hclosedSide .west hW
      · exact hclosedSide .east hE
      · exact hclosedSide .south hS
      · exact hclosedSide .north hN
    · intro k
      fin_cases k
      · exact hopenSide .west (hopen .west)
      · exact hopenSide .east (hopen .east)
      · exact hopenSide .south (hopen .south)
      · exact hopenSide .north (hopen .north)
  · rcases hwest with ⟨hWTrace, hETrace, hopenTrace⟩
    have hW : fkIsingSquareWiredPathUsesLocalSide n hn
        (setClosed e.1 omega') e .west := by
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hWTrace
    have hE : ¬fkIsingSquareWiredPathUsesLocalSide n hn
        (setClosed e.1 omega') e .east := by
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hETrace
    have hopen (side) : fkIsingSquareWiredPathUsesLocalSide n hn
        (setOpen e.1 omega') e side := by
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hopenTrace side
    exact ⟨FKIsingDobrushinDomain.PointwiseExplorationSwitchingCase.caseTwo
      (fkIsingSquareBoundary_one_visit_west_contour_balance
        n hn omega e he hW hE hopen)⟩
  · rcases heast with ⟨hWTrace, hETrace, hopenTrace⟩
    have hW : ¬fkIsingSquareWiredPathUsesLocalSide n hn
        (setClosed e.1 omega') e .west := by
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hWTrace
    have hE : fkIsingSquareWiredPathUsesLocalSide n hn
        (setClosed e.1 omega') e .east := by
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hETrace
    have hopen (side) : fkIsingSquareWiredPathUsesLocalSide n hn
        (setOpen e.1 omega') e side := by
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hopenTrace side
    exact ⟨FKIsingDobrushinDomain.PointwiseExplorationSwitchingCase.caseTwo
      (fkIsingSquareBoundary_one_visit_east_contour_balance
        n hn omega e he hW hE hopen)⟩
  · rcases hdouble with ⟨hWTrace, hETrace⟩
    have hW : fkIsingSquareWiredPathUsesLocalSide n hn
        (setClosed e.1 omega') e .west := by
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hWTrace
    have hE : fkIsingSquareWiredPathUsesLocalSide n hn
        (setClosed e.1 omega') e .east := by
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hETrace
    exact ⟨FKIsingDobrushinDomain.PointwiseExplorationSwitchingCase.caseThree
      (fkIsingSquareBoundary_double_visit_contour_balance
        n hn omega e he hW hE)⟩


end
end StatMech.Universality
