/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredClosedFibers.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredEndpoints.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredClosedFibers


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

theorem fkIsingSquare_exists_dart_endpoint
    (n : Nat) (hn : 0 < n) (u : (fkSquareBoxPlanar n).V) :
    ∃ d : FKIsingMedialDart (fkSquareBoxPlanar n),
      fkIsingSquareDartEndpoint n d = u := by
  by_cases hE : fkIsingSquareDirectionAvailable n u .east
  · exact ⟨fkIsingSquareDirectionDart n u .east hE .counterclockwise, by simp⟩
  · have hW : fkIsingSquareDirectionAvailable n u .west := by
      have hb := fkIsingSquareVertex_coordinate_bounds n u 0
      simp [fkIsingSquareDirectionAvailable] at hE ⊢
      omega
    exact ⟨fkIsingSquareDirectionDart n u .west hW .counterclockwise, by simp⟩

theorem fkIsingSquareWiredClosedComponentToPrimal_bijective
    (n : Nat) (hn : 0 < n) :
    Function.Bijective (fkIsingSquareWiredClosedComponentToPrimal n hn) := by
  constructor
  · intro C D hCD
    rw [← C.out_eq, ← D.out_eq]
    apply SimpleGraph.ConnectedComponent.sound
    apply (fkIsingSquareWiredCompleted_closed_reachable_iff_primal
      n hn C.out D.out).2
    exact SimpleGraph.ConnectedComponent.eq.mp hCD
  · intro C
    obtain ⟨d, hd⟩ := fkIsingSquare_exists_dart_endpoint n hn C.out
    let G := fkIsingSquareWiredCompletedLoopGraph n hn (FK.edgeSetConfig ∅)
    let D := G.connectedComponentMk (.dart d)
    refine ⟨D, ?_⟩
    change (openSub (fkSquareBoxPlanar n).G (FK.edgeSetConfig ∅) ⊔
      (fkIsingSquareWiredDobrushinDomain n hn).wiring).connectedComponentMk
        (fkIsingSquareWiredCarrierPrimalLabel n hn D.out) = C
    rw [← C.out_eq]
    apply SimpleGraph.ConnectedComponent.sound
    have hmed : G.Reachable D.out (.dart d) := by
      apply SimpleGraph.ConnectedComponent.eq.mp
      exact D.out_eq
    have hprim := (fkIsingSquareWiredCompleted_closed_reachable_iff_primal
      n hn D.out (.dart d)).1 hmed
    have hend :
        (openSub (fkSquareBoxPlanar n).G (FK.edgeSetConfig ∅) ⊔
          (fkIsingSquareWiredDobrushinDomain n hn).wiring).Reachable
            (fkIsingSquareWiredCarrierPrimalLabel n hn (.dart d)) C.out := by
      rw [fkIsingSquareWiredCarrierPrimalLabel, hd]
    exact hprim.trans hend


theorem fkIsingSquareWired_empty_completed_componentCount
    (n : Nat) (hn : 0 < n) :
    Nat.card (fkIsingSquareWiredCompletedLoopGraph n hn
        (FK.edgeSetConfig ∅)).ConnectedComponent =
      (2 * n + 1) ^ 2 - 2 * n := by
  rw [Nat.card_congr (Equiv.ofBijective
    (fkIsingSquareWiredClosedComponentToPrimal n hn)
    (fkIsingSquareWiredClosedComponentToPrimal_bijective n hn))]
  exact fkIsingSquareWired_empty_clusterCount n hn

theorem fkIsingSquareWiredCompleted_closed_markedA_reachable_wired_dart
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hd : fkIsingSquareWiredArc n (fkIsingSquareDartEndpoint n d)) :
    let hEA := fkIsingSquareWired_east_available_of_wired n hn
      (fkIsingSquareMarkedA n) (by
        simp [fkIsingSquareWiredArc, fkIsingSquareMarkedA])
    (fkIsingSquareWiredCompletedLoopGraph n hn (FK.edgeSetConfig ∅)).Reachable
      (.dart (fkIsingSquareDirectionDart n (fkIsingSquareMarkedA n)
        .east hEA .counterclockwise))
      (.dart d) := by
  dsimp only
  have hrotate :=
    fkIsingSquareWiredCompleted_closed_dart_reachable_east_of_wired
      n hn d hd
  dsimp only at hrotate
  rcases fkIsingSquareWiredArc_eq_markedA_or_upper n hn
    (fkIsingSquareDartEndpoint n d) hd with hA | ⟨k, hk⟩
  · have heq :
        fkIsingSquareDirectionDart n (fkIsingSquareMarkedA n) .east
            (fkIsingSquareWired_east_available_of_wired n hn _ (by
              simp [fkIsingSquareWiredArc, fkIsingSquareMarkedA]))
            .counterclockwise =
          fkIsingSquareDirectionDart n (fkIsingSquareDartEndpoint n d) .east
            (fkIsingSquareWired_east_available_of_wired n hn _ hd)
            .counterclockwise := by
      apply fkIsingSquareDirectionDart_endpoint_congr n hA.symm
    rw [heq]
    exact hrotate.symm
  · have hchain :=
        fkIsingSquareWiredCompleted_closed_markedA_reachable_upper_east
          n hn k
    dsimp only at hchain
    have heq :
        fkIsingSquareDirectionDart n
            (fkIsingSquareLeftVerticalUpper n hn k) .east
            (fkIsingSquareWired_east_available_of_wired n hn _ (by
              simp [fkIsingSquareWiredArc,
                fkIsingSquareLeftVerticalUpper])) .counterclockwise =
          fkIsingSquareDirectionDart n (fkIsingSquareDartEndpoint n d) .east
            (fkIsingSquareWired_east_available_of_wired n hn _ hd)
            .counterclockwise := by
      apply fkIsingSquareDirectionDart_endpoint_congr n hk.symm
    rw [heq] at hchain
    exact hchain.trans hrotate.symm


theorem fkIsingSquareWiredCompleted_closed_darts_reachable_of_wired
    (n : Nat) (hn : 0 < n)
    (d f : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hd : fkIsingSquareWiredArc n (fkIsingSquareDartEndpoint n d))
    (hf : fkIsingSquareWiredArc n (fkIsingSquareDartEndpoint n f)) :
    (fkIsingSquareWiredCompletedLoopGraph n hn (FK.edgeSetConfig ∅)).Reachable
      (.dart d) (.dart f) := by
  exact (fkIsingSquareWiredCompleted_closed_markedA_reachable_wired_dart
    n hn d hd).symm.trans
      (fkIsingSquareWiredCompleted_closed_markedA_reachable_wired_dart
        n hn f hf)


theorem fkIsingSquareWiredCompleted_closed_reachable_of_wired
    (n : Nat) (hn : 0 < n)
    (x y : FKIsingSquareWiredCarrier n)
    (hx : fkIsingSquareWiredArc n
      (fkIsingSquareWiredCarrierPrimalLabel n hn x))
    (hy : fkIsingSquareWiredArc n
      (fkIsingSquareWiredCarrierPrimalLabel n hn y)) :
    (fkIsingSquareWiredCompletedLoopGraph n hn (FK.edgeSetConfig ∅)).Reachable
      x y := by
  obtain ⟨d, hxd, hdx⟩ :=
    fkIsingSquareWiredCompleted_reachable_dart_same_label
      n hn (FK.edgeSetConfig ∅) x
  obtain ⟨f, hyf, hfy⟩ :=
    fkIsingSquareWiredCompleted_reachable_dart_same_label
      n hn (FK.edgeSetConfig ∅) y
  have hd : fkIsingSquareWiredArc n (fkIsingSquareDartEndpoint n d) := by
    simpa only [← hdx] using hx
  have hf : fkIsingSquareWiredArc n (fkIsingSquareDartEndpoint n f) := by
    simpa only [← hfy] using hy
  exact hxd.trans
    ((fkIsingSquareWiredCompleted_closed_darts_reachable_of_wired
      n hn d f hd hf).trans hyf.symm)

end StatMech.Universality
