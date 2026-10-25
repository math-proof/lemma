/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredExhaustive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion.Part19
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareExhaustive.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredExhaustive


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC
  StatMech.FrontierD

noncomputable section

theorem fkIsingSquareWired_closed_west_south_phase
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west) :
    (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
        (setClosed e.1 omega) (.dart (e, .south)) =
      isingLambda⁻¹ *
        (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
          (setClosed e.1 omega) (.dart (e, .west)) := by
  rw [FKIsingDobrushinDomain.windingPhase_eq_exp_turn_mul
    (fkIsingSquareWiredDobrushinDomain n hn)
    (setClosed e.1 omega) (setClosed e.1 omega)
    (.dart (e, .west)) (.dart (e, .south)) (-(Real.pi / 2))]
  · rw [FKIsingDobrushinDomain.exp_isHalf_turn_neg_pi_div_two_eq_isingLambda_inv]
  · simpa only [fkIsingSquareWiredDobrushinDomain] using
      fkIsingSquareWired_closed_west_south_winding n hn omega e h

theorem fkIsingSquareWired_closed_east_north_phase
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
        (setClosed e.1 omega) (.dart (e, .north)) =
      isingLambda⁻¹ *
        (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
          (setClosed e.1 omega) (.dart (e, .east)) := by
  rw [FKIsingDobrushinDomain.windingPhase_eq_exp_turn_mul
    (fkIsingSquareWiredDobrushinDomain n hn)
    (setClosed e.1 omega) (setClosed e.1 omega)
    (.dart (e, .east)) (.dart (e, .north)) (-(Real.pi / 2))]
  · rw [FKIsingDobrushinDomain.exp_isHalf_turn_neg_pi_div_two_eq_isingLambda_inv]
  · simpa only [fkIsingSquareWiredDobrushinDomain] using
      fkIsingSquareWired_closed_east_north_winding n hn omega e h

theorem fkIsingSquareWired_open_west_north_phase
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquareWiredPathUsesLocalSide n hn
      (setOpen e.1 omega) e .west) :
    (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
        (setOpen e.1 omega) (.dart (e, .north)) =
      isingLambda *
        (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
          (setOpen e.1 omega) (.dart (e, .west)) := by
  rw [FKIsingDobrushinDomain.windingPhase_eq_exp_turn_mul
    (fkIsingSquareWiredDobrushinDomain n hn)
    (setOpen e.1 omega) (setOpen e.1 omega)
    (.dart (e, .west)) (.dart (e, .north)) (Real.pi / 2)]
  · rw [FKIsingDobrushinDomain.exp_isHalf_turn_pi_div_two_eq_isingLambda]
  · simpa only [fkIsingSquareWiredDobrushinDomain] using
      fkIsingSquareWired_open_west_north_winding n hn omega e h

theorem fkIsingSquareWired_open_east_south_phase
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquareWiredPathUsesLocalSide n hn
      (setOpen e.1 omega) e .east) :
    (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
        (setOpen e.1 omega) (.dart (e, .south)) =
      isingLambda *
        (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
          (setOpen e.1 omega) (.dart (e, .east)) := by
  rw [FKIsingDobrushinDomain.windingPhase_eq_exp_turn_mul
    (fkIsingSquareWiredDobrushinDomain n hn)
    (setOpen e.1 omega) (setOpen e.1 omega)
    (.dart (e, .east)) (.dart (e, .south)) (Real.pi / 2)]
  · rw [FKIsingDobrushinDomain.exp_isHalf_turn_pi_div_two_eq_isingLambda]
  · simpa only [fkIsingSquareWiredDobrushinDomain] using
      fkIsingSquareWired_open_east_south_winding n hn omega e h

theorem mem_fkIsingSquareWiredDobrushinDomain_exploration_iff_order
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (z : FKIsingSquareWiredCarrier n) :
    z ∈ (fkIsingSquareWiredDobrushinDomain n hn).exploration omega ↔
      z ∈ fkIsingSquareWiredExplorationOrder n hn omega := by
  change z ∈ fkIsingSquareWiredExplorationTrace n hn omega ↔ _
  exact (mem_fkIsingSquareWiredExplorationOrder_iff_trace n hn omega z).symm


theorem fkIsingSquareWired_no_visit_pointwise_contour_balance
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hclosed : ∀ side, ¬ fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e side)
    (hopen : ∀ side, ¬ fkIsingSquareWiredPathUsesLocalSide n hn
      (setOpen e.1 omega) e side) :
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
  let D := fkIsingSquareWiredDobrushinDomain n hn
  let closed := setClosed e.1 omega
  let opened := setOpen e.1 omega
  let W : FKIsingSquareWiredCarrier n := .dart (e, .west)
  let E : FKIsingSquareWiredCarrier n := .dart (e, .east)
  let S : FKIsingSquareWiredCarrier n := .dart (e, .south)
  let N : FKIsingSquareWiredCarrier n := .dart (e, .north)
  have hc (side : FKIsingMedialSide) :
      (.dart (e, side) : FKIsingSquareWiredCarrier n) ∉
        D.exploration closed := by
    rw [mem_fkIsingSquareWiredDobrushinDomain_exploration_iff_order]
    exact hclosed side
  have ho (side : FKIsingMedialSide) :
      (.dart (e, side) : FKIsingSquareWiredCarrier n) ∉
        D.exploration opened := by
    rw [mem_fkIsingSquareWiredDobrushinDomain_exploration_iff_order]
    exact hopen side
  change (D.fermionicSummand closed W + D.fermionicSummand opened W) -
      (D.fermionicSummand closed E + D.fermionicSummand opened E) =
    Complex.I *
      ((D.fermionicSummand closed S + D.fermionicSummand opened S) -
        (D.fermionicSummand closed N + D.fermionicSummand opened N))
  unfold FKIsingDobrushinDomain.fermionicSummand
  simp [W, E, S, N, hc, ho]


theorem fkIsingSquareWired_one_visit_west_pointwise_contour_balance
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : ¬ fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east)
    (hopen : ∀ side, fkIsingSquareWiredPathUsesLocalSide n hn
      (setOpen e.1 omega) e side)
    (hseparated : ¬
      (fkIsingSquareLiftPhysicalGraph n
          (openSub (fkSquareBoxPlanar n).G (setClosed e.1 omega)) ⊔
        fkIsingSquareWiredExteriorGadget n).Reachable
          (.physical (fkIsingSquareOrientedEdge n e).tail)
          (.physical (fkIsingSquareOrientedEdge n e).head))
    (hphaseW : (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
      (setOpen e.1 omega) (.dart (e, .west)) =
        (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
          (setClosed e.1 omega) (.dart (e, .west)))
    (hphaseS : (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
      (setOpen e.1 omega) (.dart (e, .south)) =
        (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
          (setClosed e.1 omega) (.dart (e, .south))) :
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
  let a := (fkIsingSquareOrientedEdge n e).tail
  let b := (fkIsingSquareOrientedEdge n e).head
  have hab : (fkSquareBoxPlanar n).G.Adj a b := by
    rw [← SimpleGraph.mem_edgeSet, fkIsingSquareOrientedEdge_eq n e]
    exact e.2
  have hsepClique : ¬
      (openSub (fkSquareBoxPlanar n).G closed ⊔ D.wiring).Reachable a b := by
    rw [FKIsingDobrushinDomain.wiring]
    exact fun h => hseparated
      ((fkIsingSquare_openWiredExteriorGadget_reachable_iff n closed a b).2 h)
  have hcluster :
      numClustersBC (fkSquareBoxPlanar n).G D.wiring closed =
        numClustersBC (fkSquareBoxPlanar n).G D.wiring opened + 1 := by
    have h := D.numClustersBC_setClosed_eq_setOpen_add_one_of_not_reachable
      a b hab omega (by
        simpa only [a, b, closed, fkIsingSquareOrientedEdge_eq n e] using
          hsepClique)
    simpa only [a, b, closed, opened,
      fkIsingSquareOrientedEdge_eq n e] using h
  have hmass := D.sqrtTwo_mul_criticalMass_setOpen_eq_setClosed_of_clusterMerge
    (by simpa only [SimpleGraph.mem_edgeFinset] using e.2) omega hcluster
  have hmassC : (D.criticalMass closed : Complex) =
      (Real.sqrt 2 : Complex) * (D.criticalMass opened : Complex) := by
    exact_mod_cast hmass.symm
  have hcW : W ∈ D.exploration closed := by
    rw [mem_fkIsingSquareWiredDobrushinDomain_exploration_iff_order]
    exact hwest
  have hcS : S ∈ D.exploration closed := by
    exact (fkIsingSquareWired_closed_west_mem_iff_south
      n hn omega e).1 hcW
  have hcE : E ∉ D.exploration closed := by
    rw [mem_fkIsingSquareWiredDobrushinDomain_exploration_iff_order]
    exact heast
  have hcN : N ∉ D.exploration closed := by
    intro hN
    apply hcE
    exact (fkIsingSquareWired_closed_east_mem_iff_north
      n hn omega e).2 hN
  have ho (side : FKIsingMedialSide) :
      (.dart (e, side) : FKIsingSquareWiredCarrier n) ∈
        D.exploration opened := by
    rw [mem_fkIsingSquareWiredDobrushinDomain_exploration_iff_order]
    exact hopen side
  have hcSphase := fkIsingSquareWired_closed_west_south_phase
    n hn omega e hwest
  have hoNphase := fkIsingSquareWired_open_west_north_phase
    n hn omega e (hopen .west)
  have hoSphase := fkIsingSquareWired_open_east_south_phase
    n hn omega e (hopen .east)
  change (D.fermionicSummand closed W + D.fermionicSummand opened W) -
      (D.fermionicSummand closed E + D.fermionicSummand opened E) =
    Complex.I *
      ((D.fermionicSummand closed S + D.fermionicSummand opened S) -
        (D.fermionicSummand closed N + D.fermionicSummand opened N))
  unfold FKIsingDobrushinDomain.fermionicSummand
  rw [if_pos hcW, if_pos (ho .west), if_neg hcE, if_pos (ho .east),
    if_pos hcS, if_pos (ho .south), if_neg hcN, if_pos (ho .north),
    hmassC]
  simp only [zero_add]
  apply fkIsingSquare_caseTwo_westSouth_contour_algebra
  · simpa only [D, closed, W, S, fkIsingSquareWiredDobrushinDomain] using
      hcSphase
  · simpa only [D, opened, W, N, fkIsingSquareWiredDobrushinDomain] using
      hoNphase
  · simpa only [D, opened, E, S, fkIsingSquareWiredDobrushinDomain] using
      hoSphase
  · simpa only [D, opened, closed, W,
      fkIsingSquareWiredDobrushinDomain] using hphaseW
  · simpa only [D, opened, closed, S,
      fkIsingSquareWiredDobrushinDomain] using hphaseS


theorem fkIsingSquareWired_one_visit_east_pointwise_contour_balance
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : ¬ fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east)
    (hopen : ∀ side, fkIsingSquareWiredPathUsesLocalSide n hn
      (setOpen e.1 omega) e side)
    (hseparated : ¬
      (fkIsingSquareLiftPhysicalGraph n
          (openSub (fkSquareBoxPlanar n).G (setClosed e.1 omega)) ⊔
        fkIsingSquareWiredExteriorGadget n).Reachable
          (.physical (fkIsingSquareOrientedEdge n e).tail)
          (.physical (fkIsingSquareOrientedEdge n e).head))
    (hphaseE : (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
      (setOpen e.1 omega) (.dart (e, .east)) =
        (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
          (setClosed e.1 omega) (.dart (e, .east)))
    (hphaseN : (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
      (setOpen e.1 omega) (.dart (e, .north)) =
        (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
          (setClosed e.1 omega) (.dart (e, .north))) :
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
  let a := (fkIsingSquareOrientedEdge n e).tail
  let b := (fkIsingSquareOrientedEdge n e).head
  have hab : (fkSquareBoxPlanar n).G.Adj a b := by
    rw [← SimpleGraph.mem_edgeSet, fkIsingSquareOrientedEdge_eq n e]
    exact e.2
  have hsepClique : ¬
      (openSub (fkSquareBoxPlanar n).G closed ⊔ D.wiring).Reachable a b := by
    rw [FKIsingDobrushinDomain.wiring]
    exact fun h => hseparated
      ((fkIsingSquare_openWiredExteriorGadget_reachable_iff n closed a b).2 h)
  have hcluster :
      numClustersBC (fkSquareBoxPlanar n).G D.wiring closed =
        numClustersBC (fkSquareBoxPlanar n).G D.wiring opened + 1 := by
    have h := D.numClustersBC_setClosed_eq_setOpen_add_one_of_not_reachable
      a b hab omega (by
        simpa only [a, b, closed, fkIsingSquareOrientedEdge_eq n e] using
          hsepClique)
    simpa only [a, b, closed, opened,
      fkIsingSquareOrientedEdge_eq n e] using h
  have hmass := D.sqrtTwo_mul_criticalMass_setOpen_eq_setClosed_of_clusterMerge
    (by simpa only [SimpleGraph.mem_edgeFinset] using e.2) omega hcluster
  have hmassC : (D.criticalMass closed : Complex) =
      (Real.sqrt 2 : Complex) * (D.criticalMass opened : Complex) := by
    exact_mod_cast hmass.symm
  have hcE : E ∈ D.exploration closed := by
    rw [mem_fkIsingSquareWiredDobrushinDomain_exploration_iff_order]
    exact heast
  have hcN : N ∈ D.exploration closed := by
    exact (fkIsingSquareWired_closed_east_mem_iff_north
      n hn omega e).1 hcE
  have hcW : W ∉ D.exploration closed := by
    rw [mem_fkIsingSquareWiredDobrushinDomain_exploration_iff_order]
    exact hwest
  have hcS : S ∉ D.exploration closed := by
    intro hS
    apply hcW
    exact (fkIsingSquareWired_closed_west_mem_iff_south
      n hn omega e).2 hS
  have ho (side : FKIsingMedialSide) :
      (.dart (e, side) : FKIsingSquareWiredCarrier n) ∈
        D.exploration opened := by
    rw [mem_fkIsingSquareWiredDobrushinDomain_exploration_iff_order]
    exact hopen side
  have hcNphase := fkIsingSquareWired_closed_east_north_phase
    n hn omega e heast
  have hoNphase := fkIsingSquareWired_open_west_north_phase
    n hn omega e (hopen .west)
  have hoSphase := fkIsingSquareWired_open_east_south_phase
    n hn omega e (hopen .east)
  change (D.fermionicSummand closed W + D.fermionicSummand opened W) -
      (D.fermionicSummand closed E + D.fermionicSummand opened E) =
    Complex.I *
      ((D.fermionicSummand closed S + D.fermionicSummand opened S) -
        (D.fermionicSummand closed N + D.fermionicSummand opened N))
  unfold FKIsingDobrushinDomain.fermionicSummand
  rw [if_neg hcW, if_pos (ho .west), if_pos hcE, if_pos (ho .east),
    if_neg hcS, if_pos (ho .south), if_pos hcN, if_pos (ho .north),
    hmassC]
  simp only [zero_add]
  apply fkIsingSquare_caseTwo_eastNorth_contour_algebra
  · simpa only [D, closed, E, N, fkIsingSquareWiredDobrushinDomain] using
      hcNphase
  · simpa only [D, opened, W, N, fkIsingSquareWiredDobrushinDomain] using
      hoNphase
  · simpa only [D, opened, E, S, fkIsingSquareWiredDobrushinDomain] using
      hoSphase
  · simpa only [D, opened, closed, E,
      fkIsingSquareWiredDobrushinDomain] using hphaseE
  · simpa only [D, opened, closed, N,
      fkIsingSquareWiredDobrushinDomain] using hphaseN


end
end StatMech.Universality
