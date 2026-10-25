/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayer.Part8


namespace StatMech.Universality

open Finset Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareBoundary_openSub_eq_closePerimeter
    (n : Nat) (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    openSub (fkIsingSquareBoundaryDeletedPlanar n).G omega =
      openSub (fkSquareBoxPlanar n).G
        (fkIsingSquareClosePerimeter n omega) := by
  ext x y
  simp [openSub_adj, fkIsingSquareBoundaryDeletedPlanar,
    SimpleGraph.deleteEdges_adj, fkIsingSquareClosePerimeter]
  tauto

theorem fkIsingSquareClosePerimeter_setClosed
    (n : Nat) (e : Sym2 (fkSquareBoxPlanar n).V)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    fkIsingSquareClosePerimeter n (setClosed e omega) =
      setClosed e (fkIsingSquareClosePerimeter n omega) := by
  funext f
  by_cases hf : f = e
  · subst f
    simp [fkIsingSquareClosePerimeter, setClosed]
  · simp [fkIsingSquareClosePerimeter, setClosed, hf]

theorem fkIsingSquareClosePerimeter_setOpen_of_not_mem
    (n : Nat) (e : Sym2 (fkSquareBoxPlanar n).V)
    (he : e ∉ fkIsingSquarePerimeterPrimalEdgeFinset n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    fkIsingSquareClosePerimeter n (setOpen e omega) =
      setOpen e (fkIsingSquareClosePerimeter n omega) := by
  funext f
  by_cases hf : f = e
  · subst f
    simp [fkIsingSquareClosePerimeter, setOpen, he]
  · simp [fkIsingSquareClosePerimeter, setOpen, hf]

theorem fkIsingSquareBoundaryDeleted_adj_iff
    (n : Nat) (a b : (fkSquareBoxPlanar n).V) :
    (fkIsingSquareBoundaryDeletedPlanar n).G.Adj a b ↔
      (fkSquareBoxPlanar n).G.Adj a b ∧
        s(a, b) ∉ fkIsingSquarePerimeterPrimalEdgeFinset n := by
  simp [fkIsingSquareBoundaryDeletedPlanar, SimpleGraph.deleteEdges_adj]

theorem fkIsingSquareBoundary_wiring_eq_wired
    (n : Nat) (hn : 0 < n) :
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).wiring =
      (fkIsingSquareWiredDobrushinDomain n hn).wiring := rfl

theorem fkIsingSquareBoundary_openWiringGraph_eq_closePerimeter
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    openSub (fkIsingSquareBoundaryDeletedPlanar n).G omega ⊔
        (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).wiring =
      openSub (fkSquareBoxPlanar n).G
          (fkIsingSquareClosePerimeter n omega) ⊔
        (fkIsingSquareWiredDobrushinDomain n hn).wiring := by
  rw [fkIsingSquareBoundary_openSub_eq_closePerimeter,
    fkIsingSquareBoundary_wiring_eq_wired]
  rfl

theorem fkIsingSquareBoundary_numClustersBC_eq_closePerimeter
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    numClustersBC (fkIsingSquareBoundaryDeletedPlanar n).G
        (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).wiring omega =
      numClustersBC (fkSquareBoxPlanar n).G
        (fkIsingSquareWiredDobrushinDomain n hn).wiring
          (fkIsingSquareClosePerimeter n omega) := by
  unfold numClustersBC
  rw [fkIsingSquareBoundary_openWiringGraph_eq_closePerimeter]
  rfl

@[simp] theorem fkIsingSquareBoundary_windingPhase_eq_wired_closePerimeter
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (c : FKIsingSquareWiredCarrier n) :
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).windingPhase
        omega c =
      (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
        (fkIsingSquareClosePerimeter n omega) c := rfl


theorem fkIsingSquareBoundary_one_visit_west_contour_balance
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (he : e.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n)
    (hwest : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 (fkIsingSquareClosePerimeter n omega)) e .west)
    (heast : ¬fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 (fkIsingSquareClosePerimeter n omega)) e .east)
    (hopen : forall side, fkIsingSquareWiredPathUsesLocalSide n hn
      (setOpen e.1 (fkIsingSquareClosePerimeter n omega)) e side) :
    let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
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
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let omega' := fkIsingSquareClosePerimeter n omega
  let closed := setClosed e.1 omega
  let opened := setOpen e.1 omega
  let W : FKIsingSquareWiredCarrier n := .dart (e, .west)
  let E : FKIsingSquareWiredCarrier n := .dart (e, .east)
  let S : FKIsingSquareWiredCarrier n := .dart (e, .south)
  let N : FKIsingSquareWiredCarrier n := .dart (e, .north)
  let a := (fkIsingSquareOrientedEdge n e).tail
  let b := (fkIsingSquareOrientedEdge n e).head
  have habFull : (fkSquareBoxPlanar n).G.Adj a b := by
    rw [<- SimpleGraph.mem_edgeSet, fkIsingSquareOrientedEdge_eq n e]
    exact e.2
  have hedge : s(a, b) = e.1 := by
    simpa only [a, b] using fkIsingSquareOrientedEdge_eq n e
  have hclosed : setClosed s(a, b) omega = closed := by
    exact (congrArg (fun f => setClosed f omega) hedge).trans rfl
  have hopened : setOpen s(a, b) omega = opened := by
    exact (congrArg (fun f => setOpen f omega) hedge).trans rfl
  have hab : (fkIsingSquareBoundaryDeletedPlanar n).G.Adj a b := by
    apply (fkIsingSquareBoundaryDeleted_adj_iff n a b).2
    exact ⟨habFull, by
      simpa only [a, b, fkIsingSquareOrientedEdge_eq n e] using he⟩
  have hseparatedFull := fkIsingSquareWired_one_visit_separated
    n hn omega' e (Or.inl ⟨hwest, heast⟩)
  have hseparated : ¬
      (openSub (fkIsingSquareBoundaryDeletedPlanar n).G closed ⊔
        D.wiring).Reachable a b := by
    rw [fkIsingSquareBoundary_openWiringGraph_eq_closePerimeter,
      fkIsingSquareClosePerimeter_setClosed]
    simpa only [D, omega', closed, a, b] using hseparatedFull
  have hclusterFull :
      numClustersBC (fkSquareBoxPlanar n).G
          (fkIsingSquareWiredDobrushinDomain n hn).wiring
          (setClosed e.1 omega') =
        numClustersBC (fkSquareBoxPlanar n).G
          (fkIsingSquareWiredDobrushinDomain n hn).wiring
          (setOpen e.1 omega') + 1 := by
    have h := (fkIsingSquareWiredDobrushinDomain n hn).numClustersBC_setClosed_eq_setOpen_add_one_of_not_reachable
        a b habFull omega' (by
          simpa only [a, b, fkIsingSquareOrientedEdge_eq n e] using
            hseparatedFull)
    simpa only [a, b, fkIsingSquareOrientedEdge_eq n e] using h
  have hcluster :
      numClustersBC (fkIsingSquareBoundaryDeletedPlanar n).G D.wiring closed =
        numClustersBC (fkIsingSquareBoundaryDeletedPlanar n).G D.wiring opened + 1 := by
    rw [fkIsingSquareBoundary_numClustersBC_eq_closePerimeter,
      fkIsingSquareBoundary_numClustersBC_eq_closePerimeter,
      fkIsingSquareClosePerimeter_setClosed,
      fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he]
    exact hclusterFull
  have hmass := D.sqrtTwo_mul_criticalMass_setOpen_eq_setClosed_of_clusterMerge
    (by
      rw [SimpleGraph.mem_edgeFinset]
      change e.1 ∈ ((fkSquareBoxPlanar n).G.deleteEdges
        (fkIsingSquarePerimeterPrimalEdgeFinset n : Set _)).edgeSet
      rw [SimpleGraph.edgeSet_deleteEdges]
      exact ⟨e.2, by simpa using he⟩) omega hcluster
  have hmassC : (D.criticalMass closed : Complex) =
      (Real.sqrt 2 : Complex) * (D.criticalMass opened : Complex) := by
    exact_mod_cast hmass.symm
  have hcW : W ∈ D.exploration closed := by
    simpa only [D, omega', closed, W,
      fkIsingSquareBoundaryRestrictedDobrushinDomain,
      fkIsingSquareClosePerimeter_setClosed] using hwest
  have hcS : S ∈ D.exploration closed := by
    have htrace : (.dart (e, .west) : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega') := by
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hwest
    have h := (fkIsingSquareWired_closed_west_mem_iff_south
      n hn omega' e).1 htrace
    have horder : S ∈ fkIsingSquareWiredExplorationOrder n hn
        (setClosed e.1 omega') := by
      rw [mem_fkIsingSquareWiredExplorationOrder_iff_trace]
      exact h
    simpa only [D, omega', closed, S,
      fkIsingSquareBoundaryRestrictedDobrushinDomain,
      fkIsingSquareClosePerimeter_setClosed] using horder
  have hcE : E ∉ D.exploration closed := by
    simpa only [D, omega', closed, E,
      fkIsingSquareBoundaryRestrictedDobrushinDomain,
      fkIsingSquareClosePerimeter_setClosed] using heast
  have hcN : N ∉ D.exploration closed := by
    intro hN
    apply heast
    rw [fkIsingSquareWiredPathUsesLocalSide,
      mem_fkIsingSquareWiredExplorationOrder_iff_trace]
    apply (fkIsingSquareWired_closed_east_mem_iff_north n hn omega' e).2
    rw [<- mem_fkIsingSquareWiredExplorationOrder_iff_trace]
    simpa only [D, omega', closed, N,
      fkIsingSquareBoundaryRestrictedDobrushinDomain,
      fkIsingSquareClosePerimeter_setClosed] using hN
  have ho (side : FKIsingMedialSide) :
      (.dart (e, side) : FKIsingSquareWiredCarrier n) ∈
        D.exploration opened := by
    simpa only [D, omega', opened,
      fkIsingSquareBoundaryRestrictedDobrushinDomain,
      fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he] using hopen side
  have hcSphase : D.windingPhase closed S = isingLambda⁻¹ *
      D.windingPhase closed W := by
    simpa only [D, omega', closed, W, S,
      fkIsingSquareBoundary_windingPhase_eq_wired_closePerimeter,
      fkIsingSquareClosePerimeter_setClosed] using
        (fkIsingSquareWired_closed_west_south_phase n hn omega' e hwest)
  have hoNphase : D.windingPhase opened N = isingLambda *
      D.windingPhase opened W := by
    simpa only [D, omega', opened, W, N,
      fkIsingSquareBoundary_windingPhase_eq_wired_closePerimeter,
      fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he] using
        (fkIsingSquareWired_open_west_north_phase n hn omega' e (hopen .west))
  have hoSphase : D.windingPhase opened S = isingLambda *
      D.windingPhase opened E := by
    simpa only [D, omega', opened, E, S,
      fkIsingSquareBoundary_windingPhase_eq_wired_closePerimeter,
      fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he] using
        (fkIsingSquareWired_open_east_south_phase n hn omega' e (hopen .east))
  have hphaseW : D.windingPhase opened W = D.windingPhase closed W := by
    simpa only [D, omega', opened, closed, W,
      fkIsingSquareBoundary_windingPhase_eq_wired_closePerimeter,
      fkIsingSquareClosePerimeter_setClosed,
      fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he] using
        (fkIsingSquareWired_one_visit_west_phase n hn omega' e hwest heast)
  have hphaseS : D.windingPhase opened S = D.windingPhase closed S := by
    simpa only [D, omega', opened, closed, S,
      fkIsingSquareBoundary_windingPhase_eq_wired_closePerimeter,
      fkIsingSquareClosePerimeter_setClosed,
      fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he] using
        (fkIsingSquareWired_one_visit_west_inserted_phase
          n hn omega' e hwest heast)
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
  exact fkIsingSquare_caseTwo_westSouth_contour_algebra _ _ _ _ _ _ _
    hcSphase hoNphase hoSphase hphaseW hphaseS


theorem fkIsingSquareBoundary_one_visit_east_contour_balance
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (he : e.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n)
    (hwest : ¬fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 (fkIsingSquareClosePerimeter n omega)) e .west)
    (heast : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 (fkIsingSquareClosePerimeter n omega)) e .east)
    (hopen : forall side, fkIsingSquareWiredPathUsesLocalSide n hn
      (setOpen e.1 (fkIsingSquareClosePerimeter n omega)) e side) :
    let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
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
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let omega' := fkIsingSquareClosePerimeter n omega
  let closed := setClosed e.1 omega
  let opened := setOpen e.1 omega
  let W : FKIsingSquareWiredCarrier n := .dart (e, .west)
  let E : FKIsingSquareWiredCarrier n := .dart (e, .east)
  let S : FKIsingSquareWiredCarrier n := .dart (e, .south)
  let N : FKIsingSquareWiredCarrier n := .dart (e, .north)
  let a := (fkIsingSquareOrientedEdge n e).tail
  let b := (fkIsingSquareOrientedEdge n e).head
  have habFull : (fkSquareBoxPlanar n).G.Adj a b := by
    rw [<- SimpleGraph.mem_edgeSet, fkIsingSquareOrientedEdge_eq n e]
    exact e.2
  have hseparatedFull := fkIsingSquareWired_one_visit_separated
    n hn omega' e (Or.inr ⟨hwest, heast⟩)
  have hclusterFull :
      numClustersBC (fkSquareBoxPlanar n).G
          (fkIsingSquareWiredDobrushinDomain n hn).wiring
          (setClosed e.1 omega') =
        numClustersBC (fkSquareBoxPlanar n).G
          (fkIsingSquareWiredDobrushinDomain n hn).wiring
          (setOpen e.1 omega') + 1 := by
    have h := (fkIsingSquareWiredDobrushinDomain n hn).numClustersBC_setClosed_eq_setOpen_add_one_of_not_reachable
      a b habFull omega' (by
        simpa only [a, b, fkIsingSquareOrientedEdge_eq n e] using
          hseparatedFull)
    simpa only [a, b, fkIsingSquareOrientedEdge_eq n e] using h
  have hcluster :
      numClustersBC (fkIsingSquareBoundaryDeletedPlanar n).G D.wiring closed =
        numClustersBC (fkIsingSquareBoundaryDeletedPlanar n).G D.wiring opened + 1 := by
    rw [fkIsingSquareBoundary_numClustersBC_eq_closePerimeter,
      fkIsingSquareBoundary_numClustersBC_eq_closePerimeter,
      fkIsingSquareClosePerimeter_setClosed,
      fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he]
    exact hclusterFull
  have hmass := D.sqrtTwo_mul_criticalMass_setOpen_eq_setClosed_of_clusterMerge
    (by
      rw [SimpleGraph.mem_edgeFinset]
      change e.1 ∈ ((fkSquareBoxPlanar n).G.deleteEdges
        (fkIsingSquarePerimeterPrimalEdgeFinset n : Set _)).edgeSet
      rw [SimpleGraph.edgeSet_deleteEdges]
      exact ⟨e.2, by simpa using he⟩) omega hcluster
  have hmassC : (D.criticalMass closed : Complex) =
      (Real.sqrt 2 : Complex) * (D.criticalMass opened : Complex) := by
    exact_mod_cast hmass.symm
  have hcE : E ∈ D.exploration closed := by
    simpa only [D, omega', closed, E,
      fkIsingSquareBoundaryRestrictedDobrushinDomain,
      fkIsingSquareClosePerimeter_setClosed] using heast
  have hcN : N ∈ D.exploration closed := by
    have htrace : (.dart (e, .east) : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega') := by
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using heast
    have h := (fkIsingSquareWired_closed_east_mem_iff_north
      n hn omega' e).1 htrace
    have horder : N ∈ fkIsingSquareWiredExplorationOrder n hn
        (setClosed e.1 omega') := by
      rw [mem_fkIsingSquareWiredExplorationOrder_iff_trace]
      exact h
    simpa only [D, omega', closed, N,
      fkIsingSquareBoundaryRestrictedDobrushinDomain,
      fkIsingSquareClosePerimeter_setClosed] using horder
  have hcW : W ∉ D.exploration closed := by
    simpa only [D, omega', closed, W,
      fkIsingSquareBoundaryRestrictedDobrushinDomain,
      fkIsingSquareClosePerimeter_setClosed] using hwest
  have hcS : S ∉ D.exploration closed := by
    intro hS
    apply hwest
    rw [fkIsingSquareWiredPathUsesLocalSide,
      mem_fkIsingSquareWiredExplorationOrder_iff_trace]
    apply (fkIsingSquareWired_closed_west_mem_iff_south n hn omega' e).2
    rw [<- mem_fkIsingSquareWiredExplorationOrder_iff_trace]
    simpa only [D, omega', closed, S,
      fkIsingSquareBoundaryRestrictedDobrushinDomain,
      fkIsingSquareClosePerimeter_setClosed] using hS
  have ho (side : FKIsingMedialSide) :
      (.dart (e, side) : FKIsingSquareWiredCarrier n) ∈
        D.exploration opened := by
    simpa only [D, omega', opened,
      fkIsingSquareBoundaryRestrictedDobrushinDomain,
      fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he] using hopen side
  have hcNphase : D.windingPhase closed N = isingLambda⁻¹ *
      D.windingPhase closed E := by
    simpa only [D, omega', closed, E, N,
      fkIsingSquareBoundary_windingPhase_eq_wired_closePerimeter,
      fkIsingSquareClosePerimeter_setClosed] using
        (fkIsingSquareWired_closed_east_north_phase n hn omega' e heast)
  have hoNphase : D.windingPhase opened N = isingLambda *
      D.windingPhase opened W := by
    simpa only [D, omega', opened, W, N,
      fkIsingSquareBoundary_windingPhase_eq_wired_closePerimeter,
      fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he] using
        (fkIsingSquareWired_open_west_north_phase n hn omega' e (hopen .west))
  have hoSphase : D.windingPhase opened S = isingLambda *
      D.windingPhase opened E := by
    simpa only [D, omega', opened, E, S,
      fkIsingSquareBoundary_windingPhase_eq_wired_closePerimeter,
      fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he] using
        (fkIsingSquareWired_open_east_south_phase n hn omega' e (hopen .east))
  have hphaseE : D.windingPhase opened E = D.windingPhase closed E := by
    simpa only [D, omega', opened, closed, E,
      fkIsingSquareBoundary_windingPhase_eq_wired_closePerimeter,
      fkIsingSquareClosePerimeter_setClosed,
      fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he] using
        (fkIsingSquareWired_one_visit_east_phase n hn omega' e hwest heast)
  have hphaseN : D.windingPhase opened N = D.windingPhase closed N := by
    simpa only [D, omega', opened, closed, N,
      fkIsingSquareBoundary_windingPhase_eq_wired_closePerimeter,
      fkIsingSquareClosePerimeter_setClosed,
      fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he] using
        (fkIsingSquareWired_one_visit_east_inserted_phase
          n hn omega' e hwest heast)
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
  exact fkIsingSquare_caseTwo_eastNorth_contour_algebra _ _ _ _ _ _ _
    hcNphase hoNphase hoSphase hphaseE hphaseN

theorem fkIsingSquareBoundary_double_visit_open_east
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east)
    (hWN : (fkIsingSquareWiredExplorationOrder n hn
        (setClosed e.1 omega)).idxOf (.dart (e, .west)) <
      (fkIsingSquareWiredExplorationOrder n hn
        (setClosed e.1 omega)).idxOf (.dart (e, .north))) :
    fkIsingSquareWiredPathUsesLocalSide n hn
      (setOpen e.1 omega) e .east := by
  let p := fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)
  have hSW := fkIsingSquareWired_closed_south_west_oriented_infix
    n hn omega e hwest
  have hNE := fkIsingSquareWired_closed_north_east_oriented_infix
    n hn omega e heast
  have hiSW := idxOf_succ_of_pair_infix_nodup
    (fkIsingSquareWiredExplorationOrder_nodup n hn (setClosed e.1 omega)) hSW
  have hiNE := idxOf_succ_of_pair_infix_nodup
    (fkIsingSquareWiredExplorationOrder_nodup n hn (setClosed e.1 omega)) hNE
  change p.idxOf (.dart (e, .west)) = p.idxOf (.dart (e, .south)) + 1 at hiSW
  change p.idxOf (.dart (e, .east)) = p.idxOf (.dart (e, .north)) + 1 at hiNE
  rcases fkIsingSquareWired_double_visit_open_splice_support
      n hn omega e hwest heast with ⟨hsplice, _⟩ | ⟨_, hES⟩
  · change (.dart (e, .east) : FKIsingSquareWiredCarrier n) ∈
      fkIsingSquareWiredExplorationOrder n hn (setOpen e.1 omega)
    rw [hsplice, List.mem_append]
    right
    rw [List.drop_eq_getElem_cons
      (List.idxOf_lt_length_iff.mpr
        (hNE.mem (by simp : (.dart (e, .east) :
          FKIsingSquareWiredCarrier n) ∈ [(.dart (e, .north)), .dart (e, .east)]))),
      List.getElem_idxOf (List.idxOf_lt_length_iff.mpr
        (hNE.mem (by simp : (.dart (e, .east) :
          FKIsingSquareWiredCarrier n) ∈ [(.dart (e, .north)), .dart (e, .east)])))]
    simp
  · change p.idxOf (.dart (e, .east)) < p.idxOf (.dart (e, .south)) at hES
    change p.idxOf (.dart (e, .west)) < p.idxOf (.dart (e, .north)) at hWN
    omega

theorem fkIsingSquareBoundary_double_visit_open_west
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east)
    (hES : (fkIsingSquareWiredExplorationOrder n hn
        (setClosed e.1 omega)).idxOf (.dart (e, .east)) <
      (fkIsingSquareWiredExplorationOrder n hn
        (setClosed e.1 omega)).idxOf (.dart (e, .south))) :
    fkIsingSquareWiredPathUsesLocalSide n hn
      (setOpen e.1 omega) e .west := by
  let p := fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)
  have hSW := fkIsingSquareWired_closed_south_west_oriented_infix
    n hn omega e hwest
  have hNE := fkIsingSquareWired_closed_north_east_oriented_infix
    n hn omega e heast
  have hiSW := idxOf_succ_of_pair_infix_nodup
    (fkIsingSquareWiredExplorationOrder_nodup n hn (setClosed e.1 omega)) hSW
  have hiNE := idxOf_succ_of_pair_infix_nodup
    (fkIsingSquareWiredExplorationOrder_nodup n hn (setClosed e.1 omega)) hNE
  change p.idxOf (.dart (e, .west)) = p.idxOf (.dart (e, .south)) + 1 at hiSW
  change p.idxOf (.dart (e, .east)) = p.idxOf (.dart (e, .north)) + 1 at hiNE
  rcases fkIsingSquareWired_double_visit_open_splice_support
      n hn omega e hwest heast with ⟨_, hWN⟩ | ⟨hsplice, _⟩
  · change p.idxOf (.dart (e, .west)) < p.idxOf (.dart (e, .north)) at hWN
    change p.idxOf (.dart (e, .east)) < p.idxOf (.dart (e, .south)) at hES
    omega
  · change (.dart (e, .west) : FKIsingSquareWiredCarrier n) ∈
      fkIsingSquareWiredExplorationOrder n hn (setOpen e.1 omega)
    rw [hsplice, List.mem_append]
    right
    rw [List.drop_eq_getElem_cons
      (List.idxOf_lt_length_iff.mpr
        (hSW.mem (by simp : (.dart (e, .west) :
          FKIsingSquareWiredCarrier n) ∈ [(.dart (e, .south)), .dart (e, .west)]))),
      List.getElem_idxOf (List.idxOf_lt_length_iff.mpr
        (hSW.mem (by simp : (.dart (e, .west) :
          FKIsingSquareWiredCarrier n) ∈ [(.dart (e, .south)), .dart (e, .west)])))]
    simp


theorem fkIsingSquareBoundary_double_visit_contour_balance
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (he : e.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n)
    (hwest : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 (fkIsingSquareClosePerimeter n omega)) e .west)
    (heast : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 (fkIsingSquareClosePerimeter n omega)) e .east) :
    let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
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
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let omega' := fkIsingSquareClosePerimeter n omega
  let closed := setClosed e.1 omega
  let opened := setOpen e.1 omega
  let W : FKIsingSquareWiredCarrier n := .dart (e, .west)
  let E : FKIsingSquareWiredCarrier n := .dart (e, .east)
  let S : FKIsingSquareWiredCarrier n := .dart (e, .south)
  let N : FKIsingSquareWiredCarrier n := .dart (e, .north)
  let p := fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega')
  change (D.fermionicSummand closed W + D.fermionicSummand opened W) -
      (D.fermionicSummand closed E + D.fermionicSummand opened E) =
    Complex.I *
      ((D.fermionicSummand closed S + D.fermionicSummand opened S) -
        (D.fermionicSummand closed N + D.fermionicSummand opened N))
  have hSW := fkIsingSquareWired_closed_south_west_oriented_infix
    n hn omega' e hwest
  have hNE := fkIsingSquareWired_closed_north_east_oriented_infix
    n hn omega' e heast
  have hiSW := idxOf_succ_of_pair_infix_nodup
    (fkIsingSquareWiredExplorationOrder_nodup n hn (setClosed e.1 omega')) hSW
  have hiNE := idxOf_succ_of_pair_infix_nodup
    (fkIsingSquareWiredExplorationOrder_nodup n hn (setClosed e.1 omega')) hNE
  change p.idxOf W = p.idxOf S + 1 at hiSW
  change p.idxOf E = p.idxOf N + 1 at hiNE
  have hW : W ∈ D.exploration closed := by
    simpa only [D, omega', closed, W,
      fkIsingSquareBoundaryRestrictedDobrushinDomain,
      fkIsingSquareClosePerimeter_setClosed] using hwest
  have hE : E ∈ D.exploration closed := by
    simpa only [D, omega', closed, E,
      fkIsingSquareBoundaryRestrictedDobrushinDomain,
      fkIsingSquareClosePerimeter_setClosed] using heast
  have hS : S ∈ D.exploration closed := by
    have horder : S ∈ fkIsingSquareWiredExplorationOrder n hn
        (setClosed e.1 omega') := by
      simpa only [p, S] using hSW.mem (by simp)
    simpa only [D, omega', closed, S,
      fkIsingSquareBoundaryRestrictedDobrushinDomain,
      fkIsingSquareClosePerimeter_setClosed] using horder
  have hN : N ∈ D.exploration closed := by
    have horder : N ∈ fkIsingSquareWiredExplorationOrder n hn
        (setClosed e.1 omega') := by
      simpa only [p, N] using hNE.mem (by simp)
    simpa only [D, omega', closed, N,
      fkIsingSquareBoundaryRestrictedDobrushinDomain,
      fkIsingSquareClosePerimeter_setClosed] using horder
  have hclusterFull :=
    fkIsingSquareWiredExhaustive_double_visit_clusterCount_eq
      n hn omega' e hwest heast
  have hcluster :
      numClustersBC (fkIsingSquareBoundaryDeletedPlanar n).G D.wiring opened =
        numClustersBC (fkIsingSquareBoundaryDeletedPlanar n).G D.wiring closed := by
    rw [fkIsingSquareBoundary_numClustersBC_eq_closePerimeter,
      fkIsingSquareBoundary_numClustersBC_eq_closePerimeter,
      fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he,
      fkIsingSquareClosePerimeter_setClosed]
    exact hclusterFull
  have hmass := D.criticalMass_setOpen_eq_sqrtTwo_mul_setClosed_of_clusterCount_eq
    (by
      rw [SimpleGraph.mem_edgeFinset]
      change e.1 ∈ ((fkSquareBoxPlanar n).G.deleteEdges
        (fkIsingSquarePerimeterPrimalEdgeFinset n : Set _)).edgeSet
      rw [SimpleGraph.edgeSet_deleteEdges]
      exact ⟨e.2, by simpa using he⟩) omega hcluster
  have hmassC : (D.criticalMass opened : Complex) =
      (Real.sqrt 2 : Complex) * (D.criticalMass closed : Complex) := by
    exact_mod_cast hmass
  have hsource := fkIsingSquareWired_double_visit_source_side_phase
    n hn omega' e hwest heast
  rcases hsource with ⟨hWN, hphaseS'⟩ | ⟨hES, hphaseN'⟩
  · have hopenE :=
      fkIsingSquareBoundary_double_visit_open_east
        n hn omega' e hwest heast hWN
    obtain ⟨hOW', hON', hOE', hOS'⟩ :=
      (fkIsingSquareWired_double_visit_open_pair_exact
        n hn omega' e hwest heast).resolve_left (by
          rintro ⟨_, _, hnotE, _⟩
          exact hnotE hopenE)
    have hOW : W ∉ D.exploration opened := by
      simpa only [D, omega', opened, W,
        fkIsingSquareBoundaryRestrictedDobrushinDomain,
        fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he] using hOW'
    have hON : N ∉ D.exploration opened := by
      simpa only [D, omega', opened, N,
        fkIsingSquareBoundaryRestrictedDobrushinDomain,
        fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he] using hON'
    have hOE : E ∈ D.exploration opened := by
      simpa only [D, omega', opened, E,
        fkIsingSquareBoundaryRestrictedDobrushinDomain,
        fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he] using hOE'
    have hOS : S ∈ D.exploration opened := by
      simpa only [D, omega', opened, S,
        fkIsingSquareBoundaryRestrictedDobrushinDomain,
        fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he] using hOS'
    have hphaseS : D.windingPhase opened S = D.windingPhase closed S := by
      simpa only [D, omega', opened, closed, S,
        fkIsingSquareBoundary_windingPhase_eq_wired_closePerimeter,
        fkIsingSquareClosePerimeter_setClosed,
        fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he] using hphaseS'
    have hphaseE : D.windingPhase opened E = D.windingPhase closed E := by
      rcases fkIsingSquareWired_double_visit_terminal_side_phase
          n hn omega' e hwest heast with ⟨_, h⟩ | ⟨hES', _⟩
      · simpa only [D, omega', opened, closed, E,
          fkIsingSquareBoundary_windingPhase_eq_wired_closePerimeter,
          fkIsingSquareClosePerimeter_setClosed,
          fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he] using h
      · change p.idxOf E < p.idxOf S at hES'
        change p.idxOf W < p.idxOf N at hWN
        omega
    have hcS := fkIsingSquareWired_closed_west_south_phase
      n hn omega' e hwest
    have hcN := fkIsingSquareWired_closed_east_north_phase
      n hn omega' e heast
    have hoS := fkIsingSquareWired_open_east_south_phase
      n hn omega' e hopenE
    unfold FKIsingDobrushinDomain.fermionicSummand
    rw [if_pos hW, if_neg hOW, if_pos hE, if_pos hOE,
      if_pos hS, if_pos hOS, if_pos hN, if_neg hON, hmassC]
    simp only [add_zero]
    apply fkIsingSquare_caseThree_eastSouth_contour_algebra
    · simpa only [D, omega', closed, W, S,
        fkIsingSquareBoundary_windingPhase_eq_wired_closePerimeter,
        fkIsingSquareClosePerimeter_setClosed] using hcS
    · simpa only [D, omega', closed, E, N,
        fkIsingSquareBoundary_windingPhase_eq_wired_closePerimeter,
        fkIsingSquareClosePerimeter_setClosed] using hcN
    · simpa only [D, omega', opened, E, S,
        fkIsingSquareBoundary_windingPhase_eq_wired_closePerimeter,
        fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he] using hoS
    · exact hphaseS
    · exact hphaseE
  · have hopenW :=
      fkIsingSquareBoundary_double_visit_open_west
        n hn omega' e hwest heast hES
    obtain ⟨hOW', hON', hOE', hOS'⟩ :=
      (fkIsingSquareWired_double_visit_open_pair_exact
        n hn omega' e hwest heast).resolve_right (by
          rintro ⟨hnotW, _⟩
          exact hnotW hopenW)
    have hOW : W ∈ D.exploration opened := by
      simpa only [D, omega', opened, W,
        fkIsingSquareBoundaryRestrictedDobrushinDomain,
        fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he] using hOW'
    have hON : N ∈ D.exploration opened := by
      simpa only [D, omega', opened, N,
        fkIsingSquareBoundaryRestrictedDobrushinDomain,
        fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he] using hON'
    have hOE : E ∉ D.exploration opened := by
      simpa only [D, omega', opened, E,
        fkIsingSquareBoundaryRestrictedDobrushinDomain,
        fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he] using hOE'
    have hOS : S ∉ D.exploration opened := by
      simpa only [D, omega', opened, S,
        fkIsingSquareBoundaryRestrictedDobrushinDomain,
        fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he] using hOS'
    have hphaseN : D.windingPhase opened N = D.windingPhase closed N := by
      simpa only [D, omega', opened, closed, N,
        fkIsingSquareBoundary_windingPhase_eq_wired_closePerimeter,
        fkIsingSquareClosePerimeter_setClosed,
        fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he] using hphaseN'
    have hphaseW : D.windingPhase opened W = D.windingPhase closed W := by
      rcases fkIsingSquareWired_double_visit_terminal_side_phase
          n hn omega' e hwest heast with ⟨hWN', _⟩ | ⟨_, h⟩
      · change p.idxOf W < p.idxOf N at hWN'
        change p.idxOf E < p.idxOf S at hES
        omega
      · simpa only [D, omega', opened, closed, W,
          fkIsingSquareBoundary_windingPhase_eq_wired_closePerimeter,
          fkIsingSquareClosePerimeter_setClosed,
          fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he] using h
    have hcS := fkIsingSquareWired_closed_west_south_phase
      n hn omega' e hwest
    have hcN := fkIsingSquareWired_closed_east_north_phase
      n hn omega' e heast
    have hoN := fkIsingSquareWired_open_west_north_phase
      n hn omega' e hopenW
    unfold FKIsingDobrushinDomain.fermionicSummand
    rw [if_pos hW, if_pos hOW, if_pos hE, if_neg hOE,
      if_pos hS, if_neg hOS, if_pos hN, if_pos hON, hmassC]
    simp only [add_zero]
    apply fkIsingSquare_caseThree_westNorth_contour_algebra
    · simpa only [D, omega', closed, W, S,
        fkIsingSquareBoundary_windingPhase_eq_wired_closePerimeter,
        fkIsingSquareClosePerimeter_setClosed] using hcS
    · simpa only [D, omega', closed, E, N,
        fkIsingSquareBoundary_windingPhase_eq_wired_closePerimeter,
        fkIsingSquareClosePerimeter_setClosed] using hcN
    · simpa only [D, omega', opened, W, N,
        fkIsingSquareBoundary_windingPhase_eq_wired_closePerimeter,
        fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he] using hoN
    · exact hphaseN
    · exact hphaseW


end
end StatMech.Universality
