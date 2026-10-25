/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredExhaustive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion.Part19
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareExhaustive.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredExhaustive.Part2


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC
  StatMech.FrontierD

noncomputable section

theorem fkIsingSquareWiredExhaustiveBoundaryDart_endpoint_mem_wiredArc
    (n : Nat) (hn : 0 < n)
    (i : FKIsingSquareWiredBoundaryDartIndex n) :
    fkIsingSquareWiredArc n
      (fkIsingSquareDartEndpoint n
        (fkIsingSquareWiredBoundaryDart n hn i)) := by
  cases i <;>
    simp [fkIsingSquareWiredBoundaryDart, fkIsingSquareWiredArc,
      fkIsingSquareMarkedA, fkIsingSquareMarkedB,
      fkIsingSquareLeftVerticalLower, fkIsingSquareLeftVerticalUpper]


theorem fkIsingSquareWiredShiftDart_label_eq_or_wired
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareDartEndpoint n d =
        fkIsingSquareDartEndpoint n
          (fkIsingSquareWiredShiftDartEquiv n hn d) ∨
      (fkIsingSquareWiredArc n (fkIsingSquareDartEndpoint n d) ∧
        fkIsingSquareWiredArc n
          (fkIsingSquareDartEndpoint n
            (fkIsingSquareWiredShiftDartEquiv n hn d))) := by
  classical
  let f := fkIsingSquareWiredBoundaryEmbedding n hn
  by_cases hd : d ∈ Set.range f
  · obtain ⟨i, rfl⟩ := hd
    right
    have hs := fkIsingSquareWiredShiftDartEquiv_apply_boundary n hn i
    constructor
    · simpa only [f, fkIsingSquareWiredBoundaryEmbedding] using
        fkIsingSquareWiredExhaustiveBoundaryDart_endpoint_mem_wiredArc n hn i
    · change fkIsingSquareWiredArc n
        (fkIsingSquareDartEndpoint n
          (fkIsingSquareWiredShiftDartEquiv n hn
            (fkIsingSquareWiredBoundaryDart n hn i)))
      rw [hs]
      exact fkIsingSquareWiredExhaustiveBoundaryDart_endpoint_mem_wiredArc n hn
        (fkIsingSquareWiredShift n hn i)
  · left
    exact (congrArg (fkIsingSquareDartEndpoint n)
      (Equiv.Perm.viaFintypeEmbedding_apply_notMem_range
        (fkIsingSquareWiredShiftEquiv n hn) f hd)).symm

theorem fkIsingSquareWiredShiftDart_symm_label_eq_or_wired
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareDartEndpoint n d =
        fkIsingSquareDartEndpoint n
          ((fkIsingSquareWiredShiftDartEquiv n hn).symm d) ∨
      (fkIsingSquareWiredArc n (fkIsingSquareDartEndpoint n d) ∧
        fkIsingSquareWiredArc n
          (fkIsingSquareDartEndpoint n
            ((fkIsingSquareWiredShiftDartEquiv n hn).symm d))) := by
  have h := fkIsingSquareWiredShiftDart_label_eq_or_wired n hn
    ((fkIsingSquareWiredShiftDartEquiv n hn).symm d)
  rw [(fkIsingSquareWiredShiftDartEquiv n hn).apply_symm_apply] at h
  rcases h with h | ⟨hleft, hright⟩
  · exact Or.inl h.symm
  · exact Or.inr ⟨hright, hleft⟩

theorem fkIsingSquare_reachable_of_label_eq_or_wired
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y : (fkSquareBoxPlanar n).V}
    (h : x = y ∨ (fkIsingSquareWiredArc n x ∧
      fkIsingSquareWiredArc n y)) :
    (openSub (fkSquareBoxPlanar n).G omega ⊔
      (fkIsingSquareWiredDobrushinDomain n hn).wiring).Reachable x y := by
  classical
  rcases h with rfl | ⟨hx, hy⟩
  · exact SimpleGraph.Reachable.refl _
  · by_cases hxy : x = y
    · subst y
      exact SimpleGraph.Reachable.refl _
    · apply SimpleGraph.Adj.reachable
      right
      rw [FKIsingDobrushinDomain.wiring, boundaryCliqueGraph_adj]
      exact ⟨hxy, hx, hy⟩


theorem fkIsingSquareWiredExhaustiveBondMate_primalLabel_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (openSub (fkSquareBoxPlanar n).G omega ⊔
        (fkIsingSquareWiredDobrushinDomain n hn).wiring).Reachable
      (fkIsingSquareDartEndpoint n d)
      (fkIsingSquareDartEndpoint n
        (fkIsingSquareWiredBondMate n hn d)) := by
  let sigma := fkIsingSquareWiredShiftDartEquiv n hn
  let d' := sigma.symm d
  let f := fkIsingSquareBondMate n hn d'
  have h1 := fkIsingSquare_reachable_of_label_eq_or_wired n hn omega
    (fkIsingSquareWiredShiftDart_symm_label_eq_or_wired n hn d)
  have h2 : (openSub (fkSquareBoxPlanar n).G omega ⊔
        (fkIsingSquareWiredDobrushinDomain n hn).wiring).Reachable
      (fkIsingSquareDartEndpoint n d')
      (fkIsingSquareDartEndpoint n f) := by
    rw [fkIsingSquareDartEndpoint_bondMate]
  have h3 := fkIsingSquare_reachable_of_label_eq_or_wired n hn omega
    (fkIsingSquareWiredShiftDart_label_eq_or_wired n hn f)
  have hmate : fkIsingSquareWiredBondMate n hn d = sigma f := by
    dsimp only [sigma, d', f]
    rfl
  rw [hmate]
  exact h1.trans (h2.trans h3)

theorem fkIsingSquareWiredTransitionMate_primalLabel_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (x : FKIsingSquareWiredCarrier n) :
    (openSub (fkSquareBoxPlanar n).G omega ⊔
        (fkIsingSquareWiredDobrushinDomain n hn).wiring).Reachable
      (fkIsingSquareWiredExhaustiveCarrierPrimalLabel n hn x)
      (fkIsingSquareWiredExhaustiveCarrierPrimalLabel n hn
        (fkIsingSquareWiredTransitionMate n hn omega x)) := by
  cases x with
  | source =>
      change (openSub (fkSquareBoxPlanar n).G omega ⊔
          (fkIsingSquareWiredDobrushinDomain n hn).wiring).Reachable
        (fkIsingSquareMarkedA n)
        (fkIsingSquareDartEndpoint n
          (fkIsingSquareWiredBoundaryDart n hn .bottom))
      rw [show fkIsingSquareDartEndpoint n
          (fkIsingSquareWiredBoundaryDart n hn .bottom) =
          fkIsingSquareMarkedA n by
        simp [fkIsingSquareWiredBoundaryDart]]
  | terminal =>
      change (openSub (fkSquareBoxPlanar n).G omega ⊔
          (fkIsingSquareWiredDobrushinDomain n hn).wiring).Reachable
        (fkIsingSquareMarkedB n)
        (fkIsingSquareDartEndpoint n
          (fkIsingSquareWiredBoundaryDart n hn .top))
      rw [show fkIsingSquareDartEndpoint n
          (fkIsingSquareWiredBoundaryDart n hn .top) =
          fkIsingSquareMarkedB n by
        simp [fkIsingSquareWiredBoundaryDart]]
  | dart d =>
      simpa only [fkIsingSquareWiredExhaustiveCarrierPrimalLabel,
        fkIsingSquareWiredTransitionMate,
        FKIsingDobrushinDomain.wiring] using
          fkIsingSquare_localMate_primalLabel_reachable n hn omega d
  | bond d =>
      by_cases ha : d = fkIsingSquareWiredSourceDart n hn
      · subst d
        simpa [fkIsingSquareWiredExhaustiveCarrierPrimalLabel,
          fkIsingSquareWiredTransitionMate, fkIsingSquareWiredSourceDart,
          fkIsingSquareWiredBoundaryDart] using
          (SimpleGraph.Reachable.refl (fkIsingSquareMarkedA n) :
            (openSub (fkSquareBoxPlanar n).G omega ⊔
              (fkIsingSquareWiredDobrushinDomain n hn).wiring).Reachable
                (fkIsingSquareMarkedA n) (fkIsingSquareMarkedA n))
      by_cases hb : d = fkIsingSquareWiredTerminalDart n hn
      · subst d
        simp only [fkIsingSquareWiredExhaustiveCarrierPrimalLabel,
          fkIsingSquareWiredTransitionMate]
        rw [if_neg (fkIsingSquareWiredSourceDart_ne_terminalDart n hn).symm]
        simp only [if_true]
        change (openSub (fkSquareBoxPlanar n).G omega ⊔
            (fkIsingSquareWiredDobrushinDomain n hn).wiring).Reachable
          (fkIsingSquareDartEndpoint n
            (fkIsingSquareWiredBoundaryDart n hn .top))
          (fkIsingSquareMarkedB n)
        rw [show fkIsingSquareDartEndpoint n
            (fkIsingSquareWiredBoundaryDart n hn .top) =
            fkIsingSquareMarkedB n by
          simp [fkIsingSquareWiredBoundaryDart]]
      · simpa [fkIsingSquareWiredExhaustiveCarrierPrimalLabel,
          fkIsingSquareWiredTransitionMate, ha, hb] using
          fkIsingSquareWiredExhaustiveBondMate_primalLabel_reachable n hn omega d


theorem fkIsingSquareWiredExhaustiveLoopGraph_adj_primalLabel_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y : FKIsingSquareWiredCarrier n}
    (hxy : (fkIsingSquareWiredLoopGraph n hn omega).Adj x y) :
    (openSub (fkSquareBoxPlanar n).G omega ⊔
        (fkIsingSquareWiredDobrushinDomain n hn).wiring).Reachable
      (fkIsingSquareWiredExhaustiveCarrierPrimalLabel n hn x)
      (fkIsingSquareWiredExhaustiveCarrierPrimalLabel n hn y) := by
  rcases hxy with ⟨hxs, hxt, rfl⟩ | rfl
  · cases x <;> simp_all [fkIsingSquareWiredIncidenceMate,
      fkIsingSquareWiredExhaustiveCarrierPrimalLabel]
  · exact fkIsingSquareWiredTransitionMate_primalLabel_reachable
      n hn omega x

theorem fkIsingSquareWiredExhaustiveLoopGraph_walk_primalLabel_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y : FKIsingSquareWiredCarrier n}
    (p : (fkIsingSquareWiredLoopGraph n hn omega).Walk x y) :
    (openSub (fkSquareBoxPlanar n).G omega ⊔
        (fkIsingSquareWiredDobrushinDomain n hn).wiring).Reachable
      (fkIsingSquareWiredExhaustiveCarrierPrimalLabel n hn x)
      (fkIsingSquareWiredExhaustiveCarrierPrimalLabel n hn y) := by
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons u v w huv p ih =>
      exact (fkIsingSquareWiredExhaustiveLoopGraph_adj_primalLabel_reachable
        n hn omega huv).trans ih

theorem fkIsingSquareWiredExhaustiveLoopGraph_reachable_primalLabel_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y : FKIsingSquareWiredCarrier n}
    (hxy : (fkIsingSquareWiredLoopGraph n hn omega).Reachable x y) :
    (openSub (fkSquareBoxPlanar n).G omega ⊔
        (fkIsingSquareWiredDobrushinDomain n hn).wiring).Reachable
      (fkIsingSquareWiredExhaustiveCarrierPrimalLabel n hn x)
      (fkIsingSquareWiredExhaustiveCarrierPrimalLabel n hn y) := by
  obtain ⟨p⟩ := hxy
  exact fkIsingSquareWiredExhaustiveLoopGraph_walk_primalLabel_reachable n hn omega p


theorem fkIsingSquareWiredExhaustive_double_visit_closed_endpoints_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    (openSub (fkSquareBoxPlanar n).G (setClosed e.1 omega) ⊔
        (fkIsingSquareWiredDobrushinDomain n hn).wiring).Reachable
      (fkIsingSquareOrientedEdge n e).tail
      (fkIsingSquareOrientedEdge n e).head := by
  have hW : (fkIsingSquareWiredLoopGraph n hn
      (setClosed e.1 omega)).Reachable
        (.source : FKIsingSquareWiredCarrier n) (.dart (e, .west)) := by
    rw [← mem_fkIsingSquareWiredExplorationOrder_iff_reachable]
    exact hwest
  have hE : (fkIsingSquareWiredLoopGraph n hn
      (setClosed e.1 omega)).Reachable
        (.source : FKIsingSquareWiredCarrier n) (.dart (e, .east)) := by
    rw [← mem_fkIsingSquareWiredExplorationOrder_iff_reachable]
    exact heast
  have hproject := fkIsingSquareWiredExhaustiveLoopGraph_reachable_primalLabel_reachable
    n hn (setClosed e.1 omega) (hW.symm.trans hE)
  simpa [fkIsingSquareWiredExhaustiveCarrierPrimalLabel,
    fkIsingSquareDartEndpoint, fkIsingSquareSideCorner] using hproject

theorem fkIsingSquareWiredExhaustive_double_visit_clusterCount_eq
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
  have hreach := fkIsingSquareWiredExhaustive_double_visit_closed_endpoints_reachable
    n hn omega e hwest heast
  have hcount :=
    FKIsingDobrushinDomain.numClustersBC_setOpen_eq_setClosed_of_reachable
      (fkIsingSquareWiredDobrushinDomain n hn) a b hab omega (by
        simpa only [a, b, fkIsingSquareOrientedEdge_eq n e] using hreach)
  simpa only [a, b, fkIsingSquareOrientedEdge_eq n e] using hcount

theorem fkIsingSquareWiredExhaustive_double_visit_criticalMass_open_eq_sqrtTwo_mul_closed
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
    (fkIsingSquareWiredExhaustive_double_visit_clusterCount_eq
      n hn omega e hwest heast)

end
end StatMech.Universality
