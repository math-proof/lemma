/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredDoubleVisitPortGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part34
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredOpenFibers
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredDoubleVisitPortGeometry.Part2


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareWired_double_visit_discardedLoopTurn_mod_sixteen
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    FKIsingSquareWiredDiscardedLoopTurnModSixteen n hn omega e := by
  constructor
  · exact fkIsingSquareWired_double_visit_west_north_discarded_turn
      n hn omega e hwest heast
  · exact fkIsingSquareWired_double_visit_east_south_discarded_turn
      n hn omega e hwest heast


theorem fkIsingSquareWired_double_visit_source_side_phase_of_discardedLoopTurn_mod_sixteen
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east)
    (hloop : FKIsingSquareWiredDiscardedLoopTurnModSixteen n hn omega e) :
    (((fkIsingSquareWiredExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .west)) <
        (fkIsingSquareWiredExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .north))) ∧
      (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
          (setOpen e.1 omega) (.dart (e, .south)) =
        (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
          (setClosed e.1 omega) (.dart (e, .south))) ∨
    (((fkIsingSquareWiredExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .east)) <
        (fkIsingSquareWiredExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .south))) ∧
      (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
          (setOpen e.1 omega) (.dart (e, .north)) =
        (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
          (setClosed e.1 omega) (.dart (e, .north))) := by
  let D := fkIsingSquareWiredDobrushinDomain n hn
  let closed := setClosed e.1 omega
  let opened := setOpen e.1 omega
  let W : FKIsingSquareWiredCarrier n := .dart (e, .west)
  let E : FKIsingSquareWiredCarrier n := .dart (e, .east)
  let S : FKIsingSquareWiredCarrier n := .dart (e, .south)
  let N : FKIsingSquareWiredCarrier n := .dart (e, .north)
  rcases fkIsingSquareWired_double_visit_terminal_side_winding
      n hn omega e hwest heast with
    ⟨hWN, htermE⟩ | ⟨hES, htermW⟩
  · left
    refine ⟨hWN, ?_⟩
    have hturn := hloop.1 hWN
    obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp hturn
    change 8 -
        (fkIsingSquareWiredPhysicalTurnCount n hn closed N -
          fkIsingSquareWiredPhysicalTurnCount n hn closed W - 2) =
      16 * k at hk
    have hclosedNE :
        fkIsingSquareWiredPhysicalTurnCount n hn closed N =
          fkIsingSquareWiredPhysicalTurnCount n hn closed E - 2 := by
      have hraw := fkIsingSquareWired_closed_east_north_rawTurnCount
        n hn omega e heast
      change fkIsingSquareWiredRawTurnCount n hn closed N =
        fkIsingSquareWiredRawTurnCount n hn closed E - 2 at hraw
      unfold fkIsingSquareWiredPhysicalTurnCount
      rw [hraw]
      omega
    have hcount :
        fkIsingSquareWiredPhysicalTurnCount n hn closed E -
          fkIsingSquareWiredPhysicalTurnCount n hn closed W =
        12 - 16 * k := by omega
    have hwindEW :
        fkIsingSquareWiredLiftedWinding n hn closed E =
          fkIsingSquareWiredLiftedWinding n hn closed W +
            ((3 - 4 * k : Int) : Real) * Real.pi := by
      unfold fkIsingSquareWiredLiftedWinding
      rw [show fkIsingSquareWiredPhysicalTurnCount n hn closed E =
          fkIsingSquareWiredPhysicalTurnCount n hn closed W +
            (12 - 16 * k) by omega]
      push_cast
      ring
    have hopenES := fkIsingSquareWired_open_east_south_winding
      n hn omega e
        (fkIsingSquareWired_double_visit_open_east_of_west_before_north
          n hn omega e hwest heast hWN)
    have hclosedSW := fkIsingSquareWired_closed_west_south_winding
      n hn omega e hwest
    have hsource : fkIsingSquareWiredLiftedWinding n hn opened S =
        fkIsingSquareWiredLiftedWinding n hn closed S +
          ((1 - k : Int) : Real) * (4 * Real.pi) := by
      rw [hopenES, htermE, hclosedSW, hwindEW]
      push_cast
      ring
    exact FKIsingDobrushinDomain.windingPhase_eq_of_winding_eq_add_four_pi_mul_int
      D closed opened S S (1 - k) (by
        simpa only [D, closed, opened, S,
          fkIsingSquareWiredDobrushinDomain] using hsource)
  · right
    refine ⟨hES, ?_⟩
    have hturn := hloop.2 hES
    obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp hturn
    change 8 -
        (fkIsingSquareWiredPhysicalTurnCount n hn closed S -
          fkIsingSquareWiredPhysicalTurnCount n hn closed E - 2) =
      16 * k at hk
    have hclosedSW :
        fkIsingSquareWiredPhysicalTurnCount n hn closed S =
          fkIsingSquareWiredPhysicalTurnCount n hn closed W - 2 := by
      have hraw := fkIsingSquareWired_closed_west_south_rawTurnCount
        n hn omega e hwest
      change fkIsingSquareWiredRawTurnCount n hn closed S =
        fkIsingSquareWiredRawTurnCount n hn closed W - 2 at hraw
      unfold fkIsingSquareWiredPhysicalTurnCount
      rw [hraw]
      omega
    have hcount :
        fkIsingSquareWiredPhysicalTurnCount n hn closed W -
          fkIsingSquareWiredPhysicalTurnCount n hn closed E =
        12 - 16 * k := by omega
    have hwindWE :
        fkIsingSquareWiredLiftedWinding n hn closed W =
          fkIsingSquareWiredLiftedWinding n hn closed E +
            ((3 - 4 * k : Int) : Real) * Real.pi := by
      unfold fkIsingSquareWiredLiftedWinding
      rw [show fkIsingSquareWiredPhysicalTurnCount n hn closed W =
          fkIsingSquareWiredPhysicalTurnCount n hn closed E +
            (12 - 16 * k) by omega]
      push_cast
      ring
    have hopenWN := fkIsingSquareWired_open_west_north_winding
      n hn omega e
        (fkIsingSquareWired_double_visit_open_west_of_east_before_south
          n hn omega e hwest heast hES)
    have hclosedNE := fkIsingSquareWired_closed_east_north_winding
      n hn omega e heast
    have hsource : fkIsingSquareWiredLiftedWinding n hn opened N =
        fkIsingSquareWiredLiftedWinding n hn closed N +
          ((1 - k : Int) : Real) * (4 * Real.pi) := by
      rw [hopenWN, htermW, hclosedNE, hwindWE]
      push_cast
      ring
    exact FKIsingDobrushinDomain.windingPhase_eq_of_winding_eq_add_four_pi_mul_int
      D closed opened N N (1 - k) (by
        simpa only [D, closed, opened, N,
          fkIsingSquareWiredDobrushinDomain] using hsource)


theorem fkIsingSquareWired_double_visit_source_side_phase
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    (((fkIsingSquareWiredExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .west)) <
        (fkIsingSquareWiredExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .north))) ∧
      (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
          (setOpen e.1 omega) (.dart (e, .south)) =
        (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
          (setClosed e.1 omega) (.dart (e, .south))) ∨
    (((fkIsingSquareWiredExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .east)) <
        (fkIsingSquareWiredExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .south))) ∧
      (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
          (setOpen e.1 omega) (.dart (e, .north)) =
        (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
          (setClosed e.1 omega) (.dart (e, .north))) :=
  fkIsingSquareWired_double_visit_source_side_phase_of_discardedLoopTurn_mod_sixteen
    n hn omega e hwest heast
      (fkIsingSquareWired_double_visit_discardedLoopTurn_mod_sixteen
        n hn omega e hwest heast)


theorem fkIsingSquareWired_double_visit_pointwise_contour_balance
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    let D := fkIsingSquareWiredDobrushinDomain n hn
    let closed := setClosed e.1 omega
    let opened := setOpen e.1 omega
    let W : FKIsingSquareWiredCarrier n := .dart (e, .west)
    let E : FKIsingSquareWiredCarrier n := .dart (e, .east)
    let S : FKIsingSquareWiredCarrier n := .dart (e, .south)
    let N : FKIsingSquareWiredCarrier n := .dart (e, .north)
    (D.fermionicSummand closed W + D.fermionicSummand opened W) -
        (D.fermionicSummand closed E + D.fermionicSummand opened E) =
      Complex.I *
        ((D.fermionicSummand closed S + D.fermionicSummand opened S) -
          (D.fermionicSummand closed N + D.fermionicSummand opened N)) := by
  classical
  let D := fkIsingSquareWiredDobrushinDomain n hn
  let closed := setClosed e.1 omega
  let opened := setOpen e.1 omega
  let W : FKIsingSquareWiredCarrier n := .dart (e, .west)
  let E : FKIsingSquareWiredCarrier n := .dart (e, .east)
  let S : FKIsingSquareWiredCarrier n := .dart (e, .south)
  let N : FKIsingSquareWiredCarrier n := .dart (e, .north)
  let p := fkIsingSquareWiredExplorationOrder n hn closed
  change (D.fermionicSummand closed W + D.fermionicSummand opened W) -
      (D.fermionicSummand closed E + D.fermionicSummand opened E) =
    Complex.I *
      ((D.fermionicSummand closed S + D.fermionicSummand opened S) -
        (D.fermionicSummand closed N + D.fermionicSummand opened N))
  have hSW := fkIsingSquareWired_closed_south_west_oriented_infix
    n hn omega e hwest
  have hNE := fkIsingSquareWired_closed_north_east_oriented_infix
    n hn omega e heast
  have hiSW := idxOf_succ_of_pair_infix_nodup
    (fkIsingSquareWiredExplorationOrder_nodup n hn closed) hSW
  have hiNE := idxOf_succ_of_pair_infix_nodup
    (fkIsingSquareWiredExplorationOrder_nodup n hn closed) hNE
  change p.idxOf W = p.idxOf S + 1 at hiSW
  change p.idxOf E = p.idxOf N + 1 at hiNE
  have hW : W ∈ D.exploration closed := by
    rw [mem_fkIsingSquareWiredDobrushinDomain_exploration_iff_order]
    exact hwest
  have hE : E ∈ D.exploration closed := by
    rw [mem_fkIsingSquareWiredDobrushinDomain_exploration_iff_order]
    exact heast
  have hS : S ∈ D.exploration closed := by
    rw [mem_fkIsingSquareWiredDobrushinDomain_exploration_iff_order]
    simpa only [p, closed, S] using hSW.mem (by simp)
  have hN : N ∈ D.exploration closed := by
    rw [mem_fkIsingSquareWiredDobrushinDomain_exploration_iff_order]
    simpa only [p, closed, N] using hNE.mem (by simp)
  have hmass :=
    fkIsingSquareWiredExhaustive_double_visit_criticalMass_open_eq_sqrtTwo_mul_closed
      n hn omega e hwest heast
  have hmassC : (D.criticalMass opened : Complex) =
      (Real.sqrt 2 : Complex) * (D.criticalMass closed : Complex) := by
    exact_mod_cast hmass
  have hsource := fkIsingSquareWired_double_visit_source_side_phase
    n hn omega e hwest heast
  rcases hsource with ⟨hWN, hphaseS⟩ | ⟨hES, hphaseN⟩
  · have hopenE :=
      fkIsingSquareWired_double_visit_open_east_of_west_before_north
        n hn omega e hwest heast hWN
    obtain ⟨hOW', hON', hOE', hOS'⟩ :=
      (fkIsingSquareWired_double_visit_open_pair_exact
        n hn omega e hwest heast).resolve_left (by
          rintro ⟨_, _, hnotE, _⟩
          exact hnotE hopenE)
    have hOW : W ∉ D.exploration opened := by
      rw [mem_fkIsingSquareWiredDobrushinDomain_exploration_iff_order]
      exact hOW'
    have hON : N ∉ D.exploration opened := by
      rw [mem_fkIsingSquareWiredDobrushinDomain_exploration_iff_order]
      exact hON'
    have hOE : E ∈ D.exploration opened := by
      rw [mem_fkIsingSquareWiredDobrushinDomain_exploration_iff_order]
      exact hOE'
    have hOS : S ∈ D.exploration opened := by
      rw [mem_fkIsingSquareWiredDobrushinDomain_exploration_iff_order]
      exact hOS'
    have hphaseE : D.windingPhase opened E = D.windingPhase closed E := by
      rcases fkIsingSquareWired_double_visit_terminal_side_phase
          n hn omega e hwest heast with ⟨_, h⟩ | ⟨hES', _⟩
      · simpa only [D, opened, closed, E,
          fkIsingSquareWiredDobrushinDomain] using h
      · change p.idxOf E < p.idxOf S at hES'
        change p.idxOf W < p.idxOf N at hWN
        omega
    have hcS := fkIsingSquareWired_closed_west_south_phase
      n hn omega e hwest
    have hcN := fkIsingSquareWired_closed_east_north_phase
      n hn omega e heast
    have hoS := fkIsingSquareWired_open_east_south_phase
      n hn omega e hopenE
    unfold FKIsingDobrushinDomain.fermionicSummand
    rw [if_pos hW, if_neg hOW, if_pos hE, if_pos hOE,
      if_pos hS, if_pos hOS, if_pos hN, if_neg hON, hmassC]
    simp only [add_zero]
    apply fkIsingSquare_caseThree_eastSouth_contour_algebra
    · simpa only [D, closed, W, S,
        fkIsingSquareWiredDobrushinDomain] using hcS
    · simpa only [D, closed, E, N,
        fkIsingSquareWiredDobrushinDomain] using hcN
    · simpa only [D, opened, E, S,
        fkIsingSquareWiredDobrushinDomain] using hoS
    · exact hphaseS
    · exact hphaseE
  · have hopenW :=
      fkIsingSquareWired_double_visit_open_west_of_east_before_south
        n hn omega e hwest heast hES
    obtain ⟨hOW', hON', hOE', hOS'⟩ :=
      (fkIsingSquareWired_double_visit_open_pair_exact
        n hn omega e hwest heast).resolve_right (by
          rintro ⟨hnotW, _⟩
          exact hnotW hopenW)
    have hOW : W ∈ D.exploration opened := by
      rw [mem_fkIsingSquareWiredDobrushinDomain_exploration_iff_order]
      exact hOW'
    have hON : N ∈ D.exploration opened := by
      rw [mem_fkIsingSquareWiredDobrushinDomain_exploration_iff_order]
      exact hON'
    have hOE : E ∉ D.exploration opened := by
      rw [mem_fkIsingSquareWiredDobrushinDomain_exploration_iff_order]
      exact hOE'
    have hOS : S ∉ D.exploration opened := by
      rw [mem_fkIsingSquareWiredDobrushinDomain_exploration_iff_order]
      exact hOS'
    have hphaseW : D.windingPhase opened W = D.windingPhase closed W := by
      rcases fkIsingSquareWired_double_visit_terminal_side_phase
          n hn omega e hwest heast with ⟨hWN', _⟩ | ⟨_, h⟩
      · change p.idxOf W < p.idxOf N at hWN'
        change p.idxOf E < p.idxOf S at hES
        omega
      · simpa only [D, opened, closed, W,
          fkIsingSquareWiredDobrushinDomain] using h
    have hcS := fkIsingSquareWired_closed_west_south_phase
      n hn omega e hwest
    have hcN := fkIsingSquareWired_closed_east_north_phase
      n hn omega e heast
    have hoN := fkIsingSquareWired_open_west_north_phase
      n hn omega e hopenW
    unfold FKIsingDobrushinDomain.fermionicSummand
    rw [if_pos hW, if_pos hOW, if_pos hE, if_neg hOE,
      if_pos hS, if_neg hOS, if_pos hN, if_pos hON, hmassC]
    simp only [add_zero]
    apply fkIsingSquare_caseThree_westNorth_contour_algebra
    · simpa only [D, closed, W, S,
        fkIsingSquareWiredDobrushinDomain] using hcS
    · simpa only [D, closed, E, N,
        fkIsingSquareWiredDobrushinDomain] using hcN
    · simpa only [D, opened, W, N,
        fkIsingSquareWiredDobrushinDomain] using hoN
    · exact hphaseN
    · exact hphaseW


end
end StatMech.Universality
