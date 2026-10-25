/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion.Part19
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareExhaustive.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredSwitching
open Finset Complex


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC
  StatMech.FrontierD

noncomputable section

theorem fkIsingSquareWiredBoundaryDart_endpoint_mem_wiredArc
    (n : Nat) (hn : 0 < n)
    (i : FKIsingSquareWiredBoundaryDartIndex n) :
    fkIsingSquareWiredArc n
      (fkIsingSquareDartEndpoint n
        (fkIsingSquareWiredBoundaryDart n hn i)) := by
  cases i with
  | bottom =>
      simp [fkIsingSquareWiredBoundaryDart,
        fkIsingSquareMarkedA, fkIsingSquareWiredArc]
  | west k =>
      simp [fkIsingSquareWiredBoundaryDart,
        fkIsingSquareLeftVerticalLower, fkIsingSquareWiredArc]
  | north k =>
      simp [fkIsingSquareWiredBoundaryDart,
        fkIsingSquareLeftVerticalUpper, fkIsingSquareWiredArc]
  | top =>
      simp [fkIsingSquareWiredBoundaryDart,
        fkIsingSquareMarkedB, fkIsingSquareWiredArc]

theorem fkIsingSquareWiredShiftDart_primalLabel_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (openSub (fkSquareBoxPlanar n).G omega ⊔
        boundaryCliqueGraph (fkIsingSquareWiredArc n)).Reachable
      (fkIsingSquareDartEndpoint n d)
      (fkIsingSquareDartEndpoint n
        (fkIsingSquareWiredShiftDartEquiv n hn d)) := by
  classical
  by_cases hd : d ∈ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)
  · obtain ⟨i, rfl⟩ := hd
    simp only [fkIsingSquareWiredShiftDartEquiv,
      Equiv.Perm.viaFintypeEmbedding_apply_image]
    change (openSub (fkSquareBoxPlanar n).G omega ⊔
        boundaryCliqueGraph (fkIsingSquareWiredArc n)).Reachable
      (fkIsingSquareDartEndpoint n
        (fkIsingSquareWiredBoundaryDart n hn i))
      (fkIsingSquareDartEndpoint n
        (fkIsingSquareWiredBoundaryDart n hn
          (fkIsingSquareWiredShiftEquiv n hn i)))
    by_cases hlabel : fkIsingSquareDartEndpoint n
        (fkIsingSquareWiredBoundaryDart n hn i) =
      fkIsingSquareDartEndpoint n
        (fkIsingSquareWiredBoundaryDart n hn
          (fkIsingSquareWiredShiftEquiv n hn i))
    · rw [hlabel]
    · apply SimpleGraph.Adj.reachable
      right
      rw [boundaryCliqueGraph_adj]
      exact ⟨hlabel,
        fkIsingSquareWiredBoundaryDart_endpoint_mem_wiredArc n hn i,
        fkIsingSquareWiredBoundaryDart_endpoint_mem_wiredArc n hn
          (fkIsingSquareWiredShiftEquiv n hn i)⟩
  · simp only [fkIsingSquareWiredShiftDartEquiv,
      Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ _ hd]
    exact SimpleGraph.Reachable.refl _

theorem fkIsingSquareWiredShiftDart_symm_primalLabel_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (openSub (fkSquareBoxPlanar n).G omega ⊔
        boundaryCliqueGraph (fkIsingSquareWiredArc n)).Reachable
      (fkIsingSquareDartEndpoint n d)
      (fkIsingSquareDartEndpoint n
        ((fkIsingSquareWiredShiftDartEquiv n hn).symm d)) := by
  have h := fkIsingSquareWiredShiftDart_primalLabel_reachable n hn omega
    ((fkIsingSquareWiredShiftDartEquiv n hn).symm d)
  simpa using h.symm


theorem fkIsingSquareWiredBondMate_primalLabel_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (openSub (fkSquareBoxPlanar n).G omega ⊔
        boundaryCliqueGraph (fkIsingSquareWiredArc n)).Reachable
      (fkIsingSquareDartEndpoint n d)
      (fkIsingSquareDartEndpoint n
        (fkIsingSquareWiredBondMate n hn d)) := by
  let S := fkIsingSquareWiredShiftDartEquiv n hn
  let d' := S.symm d
  let f' := fkIsingSquareBondMate n hn d'
  have hS := fkIsingSquareWiredShiftDart_symm_primalLabel_reachable
    n hn omega d
  have hB : fkIsingSquareDartEndpoint n d' =
      fkIsingSquareDartEndpoint n f' := by
    exact (fkIsingSquareDartEndpoint_bondMate n hn d').symm
  have hS' := fkIsingSquareWiredShiftDart_primalLabel_reachable
    n hn omega f'
  have hS0 :
      (openSub (fkSquareBoxPlanar n).G omega ⊔
          boundaryCliqueGraph (fkIsingSquareWiredArc n)).Reachable
        (fkIsingSquareDartEndpoint n d)
        (fkIsingSquareDartEndpoint n d') := by
    simpa only [d', S] using hS
  have hB0 :
      (openSub (fkSquareBoxPlanar n).G omega ⊔
          boundaryCliqueGraph (fkIsingSquareWiredArc n)).Reachable
        (fkIsingSquareDartEndpoint n d')
        (fkIsingSquareDartEndpoint n f') := by
    rw [hB]
  have hout : fkIsingSquareWiredBondMate n hn d = S f' := by
    rfl
  rw [hout]
  exact hS0.trans (hB0.trans (by simpa only [S, f'] using hS'))

theorem fkIsingSquareWiredTransitionMate_primalLabel_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (x : FKIsingSquareWiredCarrier n) :
    (openSub (fkSquareBoxPlanar n).G omega ⊔
        boundaryCliqueGraph (fkIsingSquareWiredArc n)).Reachable
      (fkIsingSquareWiredCarrierPrimalLabel n hn x)
      (fkIsingSquareWiredCarrierPrimalLabel n hn
        (fkIsingSquareWiredTransitionMate n hn omega x)) := by
  cases x with
  | source =>
      simp [fkIsingSquareWiredCarrierPrimalLabel,
        fkIsingSquareWiredTransitionMate,
        fkIsingSquareWiredSourceDart,
        fkIsingSquareWiredBoundaryDart]
  | terminal =>
      have hne := (fkIsingSquareWiredSourceDart_ne_terminalDart n hn).symm
      simp only [fkIsingSquareWiredTransitionMate, hne, ↓reduceIte]
      simp [fkIsingSquareWiredCarrierPrimalLabel,
        fkIsingSquareWiredTerminalDart,
        fkIsingSquareWiredBoundaryDart]
  | dart d =>
      simpa [fkIsingSquareWiredCarrierPrimalLabel,
        FKIsingDobrushinDomain.wiring,
        fkIsingSquareWiredDobrushinDomain] using
        (fkIsingSquare_localMate_primalLabel_reachable n hn omega d)
  | bond d =>
      by_cases ha : d = fkIsingSquareWiredSourceDart n hn
      · subst d
        simp [fkIsingSquareWiredCarrierPrimalLabel,
          fkIsingSquareWiredTransitionMate,
          fkIsingSquareWiredSourceDart,
          fkIsingSquareWiredBoundaryDart]
      by_cases hb : d = fkIsingSquareWiredTerminalDart n hn
      · subst d
        have hne := (fkIsingSquareWiredSourceDart_ne_terminalDart n hn).symm
        simp only [fkIsingSquareWiredTransitionMate, hne, ↓reduceIte]
        simp [fkIsingSquareWiredCarrierPrimalLabel,
          fkIsingSquareWiredTerminalDart,
          fkIsingSquareWiredBoundaryDart]
      · simpa [fkIsingSquareWiredCarrierPrimalLabel,
          fkIsingSquareWiredTransitionMate, ha, hb] using
          (fkIsingSquareWiredBondMate_primalLabel_reachable
            n hn omega d)


theorem fkIsingSquareWiredLoopGraph_adj_primalLabel_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y : FKIsingSquareWiredCarrier n}
    (hxy : (fkIsingSquareWiredLoopGraph n hn omega).Adj x y) :
    (openSub (fkSquareBoxPlanar n).G omega ⊔
        boundaryCliqueGraph (fkIsingSquareWiredArc n)).Reachable
      (fkIsingSquareWiredCarrierPrimalLabel n hn x)
      (fkIsingSquareWiredCarrierPrimalLabel n hn y) := by
  rcases hxy with ⟨hxs, hxt, rfl⟩ | rfl
  · cases x <;>
      simp_all [fkIsingSquareWiredIncidenceMate,
        fkIsingSquareWiredCarrierPrimalLabel]
  · exact fkIsingSquareWiredTransitionMate_primalLabel_reachable
      n hn omega x

theorem fkIsingSquareWiredLoopGraph_walk_primalLabel_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y : FKIsingSquareWiredCarrier n}
    (p : (fkIsingSquareWiredLoopGraph n hn omega).Walk x y) :
    (openSub (fkSquareBoxPlanar n).G omega ⊔
        boundaryCliqueGraph (fkIsingSquareWiredArc n)).Reachable
      (fkIsingSquareWiredCarrierPrimalLabel n hn x)
      (fkIsingSquareWiredCarrierPrimalLabel n hn y) := by
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons u v w huv p ih =>
      exact (fkIsingSquareWiredLoopGraph_adj_primalLabel_reachable
        n hn omega huv).trans ih


theorem fkIsingSquareWiredLoopGraph_reachable_primalLabel_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y : FKIsingSquareWiredCarrier n}
    (hxy : (fkIsingSquareWiredLoopGraph n hn omega).Reachable x y) :
    (openSub (fkSquareBoxPlanar n).G omega ⊔
        boundaryCliqueGraph (fkIsingSquareWiredArc n)).Reachable
      (fkIsingSquareWiredCarrierPrimalLabel n hn x)
      (fkIsingSquareWiredCarrierPrimalLabel n hn y) := by
  obtain ⟨p⟩ := hxy
  exact fkIsingSquareWiredLoopGraph_walk_primalLabel_reachable
    n hn omega p


theorem fkIsingSquareWired_double_visit_closed_endpoints_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    (openSub (fkSquareBoxPlanar n).G (setClosed e.1 omega) ⊔
        boundaryCliqueGraph (fkIsingSquareWiredArc n)).Reachable
      (fkIsingSquareOrientedEdge n e).tail
      (fkIsingSquareOrientedEdge n e).head := by
  have hW : (fkIsingSquareWiredLoopGraph n hn
      (setClosed e.1 omega)).Reachable
      (.source : FKIsingSquareWiredCarrier n) (.dart (e, .west)) := by
    rw [← fkIsingSquareWiredPath_mem_support_iff_reachable n hn
      (setClosed e.1 omega)
      (fkIsingSquareWiredExplorationPath n hn (setClosed e.1 omega))
      (fkIsingSquareWiredExplorationPath n hn
        (setClosed e.1 omega)).isPath]
    exact hwest
  have hE : (fkIsingSquareWiredLoopGraph n hn
      (setClosed e.1 omega)).Reachable
      (.source : FKIsingSquareWiredCarrier n) (.dart (e, .east)) := by
    rw [← fkIsingSquareWiredPath_mem_support_iff_reachable n hn
      (setClosed e.1 omega)
      (fkIsingSquareWiredExplorationPath n hn (setClosed e.1 omega))
      (fkIsingSquareWiredExplorationPath n hn
        (setClosed e.1 omega)).isPath]
    exact heast
  have hproject :=
    fkIsingSquareWiredLoopGraph_reachable_primalLabel_reachable
      n hn (setClosed e.1 omega) (hW.symm.trans hE)
  simpa [fkIsingSquareWiredCarrierPrimalLabel,
    fkIsingSquareDartEndpoint, fkIsingSquareSideCorner] using hproject


theorem fkIsingSquareWiredCompletedLoopGraph_reachable_iff
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (x y : FKIsingSquareWiredCarrier n) :
    (fkIsingSquareWiredCompletedLoopGraph n hn omega).Reachable x y ↔
      (fkIsingSquareWiredLoopGraph n hn omega).Reachable x y := by
  rw [fkIsingSquareWiredCompletedLoopGraph, reachable_sup_edge_iff]
  constructor
  · rintro (hxy | ⟨hxs, hty⟩ | ⟨hxt, hsy⟩)
    · exact hxy
    · exact hxs.trans
        ((fkIsingSquareWiredLoopGraph_source_reachable_terminal
          n hn omega).trans hty)
    · exact hxt.trans
        ((fkIsingSquareWiredLoopGraph_source_reachable_terminal
          n hn omega).symm.trans hsy)
  · exact Or.inl


theorem fkIsingSquareWired_one_visit_completedLoop_componentCount
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hone :
      (fkIsingSquareWiredPathUsesLocalSide n hn
          (setClosed e.1 omega) e .west ∧
        ¬ fkIsingSquareWiredPathUsesLocalSide n hn
          (setClosed e.1 omega) e .east) ∨
      (¬ fkIsingSquareWiredPathUsesLocalSide n hn
          (setClosed e.1 omega) e .west ∧
        fkIsingSquareWiredPathUsesLocalSide n hn
          (setClosed e.1 omega) e .east)) :
    Nat.card (fkIsingSquareWiredCompletedLoopGraph n hn
        (setOpen e.1 omega)).ConnectedComponent + 1 =
      Nat.card (fkIsingSquareWiredCompletedLoopGraph n hn
        (setClosed e.1 omega)).ConnectedComponent := by
  let G := fkIsingSquareWiredCompletedLoopGraph n hn
    (setClosed e.1 omega)
  let W : FKIsingSquareWiredCarrier n := .dart (e, .west)
  let E : FKIsingSquareWiredCarrier n := .dart (e, .east)
  let S : FKIsingSquareWiredCarrier n := .dart (e, .south)
  let N : FKIsingSquareWiredCarrier n := .dart (e, .north)
  have hWS : G.Adj W S := by
    simpa only [G, W, S] using
      fkIsingSquareWiredCompletedLoopGraph_closed_west_south_adj
        n hn omega e
  have hEN : G.Adj E N := by
    simpa only [G, E, N] using
      fkIsingSquareWiredCompletedLoopGraph_closed_east_north_adj
        n hn omega e
  have hdisc : ¬ G.Reachable W E := by
    rcases hone with ⟨hW, hE⟩ | ⟨hW, hE⟩
    · intro hWE
      apply hE
      have hsW : (fkIsingSquareWiredLoopGraph n hn
          (setClosed e.1 omega)).Reachable .source W := by
        rw [← mem_fkIsingSquareWiredExplorationOrder_iff_reachable]
        simpa only [fkIsingSquareWiredPathUsesLocalSide, W] using hW
      have hWE' : (fkIsingSquareWiredLoopGraph n hn
          (setClosed e.1 omega)).Reachable W E :=
        (fkIsingSquareWiredCompletedLoopGraph_reachable_iff
          n hn (setClosed e.1 omega) W E).1 hWE
      rw [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_reachable]
      simpa only [E] using hsW.trans hWE'
    · intro hWE
      apply hW
      have hsE : (fkIsingSquareWiredLoopGraph n hn
          (setClosed e.1 omega)).Reachable .source E := by
        rw [← mem_fkIsingSquareWiredExplorationOrder_iff_reachable]
        simpa only [fkIsingSquareWiredPathUsesLocalSide, E] using hE
      have hWE' : (fkIsingSquareWiredLoopGraph n hn
          (setClosed e.1 omega)).Reachable W E :=
        (fkIsingSquareWiredCompletedLoopGraph_reachable_iff
          n hn (setClosed e.1 omega) W E).1 hWE
      rw [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_reachable]
      simpa only [W] using hsE.trans hWE'.symm
  have hcount := StatMech.FrontierD.card_components_twoEdgeSwitch_of_not_reachable
    G (fkIsingSquareWiredCompletedLoopGraph_even_degree n hn
      (setClosed e.1 omega)) hWS hEN hdisc
  rw [fkIsingSquareWiredCompletedLoopGraph_setOpen_eq_twoEdgeSwitch
    n hn omega e]
  simpa only [G, W, S, E, N, medialTwoEdgeSwitch] using hcount


theorem fkIsingSquareWired_double_visit_clusterCount_eq
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    numClustersBC (fkSquareBoxPlanar n).G
        (fkIsingSquareWiredDobrushinDomain n hn).wiring
        (setOpen e.1 omega) =
      numClustersBC (fkSquareBoxPlanar n).G
        (fkIsingSquareWiredDobrushinDomain n hn).wiring
        (setClosed e.1 omega) := by
  let a := (fkIsingSquareOrientedEdge n e).tail
  let b := (fkIsingSquareOrientedEdge n e).head
  have hab : (fkSquareBoxPlanar n).G.Adj a b := by
    rw [← SimpleGraph.mem_edgeSet, fkIsingSquareOrientedEdge_eq n e]
    exact e.2
  have hreach := fkIsingSquareWired_double_visit_closed_endpoints_reachable
    n hn omega e hwest heast
  have hcount :=
    FKIsingDobrushinDomain.numClustersBC_setOpen_eq_setClosed_of_reachable
      (fkIsingSquareWiredDobrushinDomain n hn) a b hab omega (by
        simpa only [a, b, FKIsingDobrushinDomain.wiring,
          fkIsingSquareWiredDobrushinDomain,
          fkIsingSquareOrientedEdge_eq n e] using hreach)
  simpa only [a, b, fkIsingSquareOrientedEdge_eq n e] using hcount


theorem fkIsingSquareWired_double_visit_criticalMass_open_eq_sqrtTwo_mul_closed
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    (fkIsingSquareWiredDobrushinDomain n hn).criticalMass
        (setOpen e.1 omega) =
      Real.sqrt 2 *
        (fkIsingSquareWiredDobrushinDomain n hn).criticalMass
          (setClosed e.1 omega) := by
  exact FKIsingDobrushinDomain.criticalMass_setOpen_eq_sqrtTwo_mul_setClosed_of_clusterCount_eq
    (fkIsingSquareWiredDobrushinDomain n hn)
    (by simpa only [SimpleGraph.mem_edgeFinset] using e.2) omega
    (fkIsingSquareWired_double_visit_clusterCount_eq
      n hn omega e hwest heast)


end
end StatMech.Universality
