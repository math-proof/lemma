/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredEndpoints.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredEuler
import Theorem.StatisticalMechanics.Code.FK.EdgeConfigZ.Part15
import Theorem.StatisticalMechanics.Code.FrontierB.BoxGraphPath.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredEndpoints.Part2
open Finset SimpleGraph


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierB
  StatMech.FrontierD

noncomputable section

theorem fkIsingSquareWiredArc_card (n : Nat) :
    Nat.card
      {x : (fkSquareBoxPlanar n).V // fkIsingSquareWiredArc n x} =
      2 * n + 1 := by
  rw [Nat.card_congr (fkIsingSquareWiredArcEquivIcc n),
    Nat.card_eq_fintype_card, Fintype.card_coe, Int.card_Icc]
  omega

theorem fkIsingSquareWired_empty_clusterCount
    (n : Nat) (hn : 0 < n) :
    numClustersBC (fkSquareBoxPlanar n).G
        (fkIsingSquareWiredDobrushinDomain n hn).wiring
        (FK.edgeSetConfig ∅) =
      (2 * n + 1) ^ 2 - 2 * n := by
  classical
  have hopen : openSub (fkSquareBoxPlanar n).G (FK.edgeSetConfig ∅) = ⊥ := by
    ext x y
    simp [FK.edgeSetConfig]
  unfold FKIsingDobrushinDomain.wiring
  rw [fkIsingSquareWiredDobrushinDomain]
  unfold numClustersBC
  rw [hopen, bot_sup_eq]
  change Nat.card
      (boundaryCliqueGraph (fkIsingSquareWiredArc n)).ConnectedComponent = _
  rw [card_boundaryCliqueGraph_components
    (fkIsingSquareWiredArc n) (fkIsingSquareMarkedA n)
    (fkIsingSquareMarkedA_mem_wiredArc n)]
  have hArc : Fintype.card
      {x : (fkSquareBoxPlanar n).V // fkIsingSquareWiredArc n x} =
        2 * n + 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact fkIsingSquareWiredArc_card n
  have hV : Fintype.card (fkSquareBoxPlanar n).V =
      (2 * n + 1) ^ 2 := by
    change Fintype.card (StatMech.FK.boxVerts 2 n) = _
    exact StatMech.FK.ecz_boxVerts_card 2 n
  rw [Fintype.card_subtype_compl, hArc, hV]
  have hle : 2 * n + 1 ≤ (2 * n + 1) ^ 2 := by nlinarith
  omega

theorem fkIsingSquareWired_full_clusterCount
    (n : Nat) (hn : 0 < n) :
    numClustersBC (fkSquareBoxPlanar n).G
        (fkIsingSquareWiredDobrushinDomain n hn).wiring
        (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset) = 1 := by
  have hopen : openSub (fkSquareBoxPlanar n).G
      (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset) =
        (fkSquareBoxPlanar n).G := by
    ext x y
    simp only [openSub_adj, FK.edgeSetConfig_apply,
      SimpleGraph.mem_edgeFinset]
    tauto
  unfold numClustersBC
  rw [hopen]
  apply card_components_eq_one_of_connected
  apply SimpleGraph.Connected.mono
    (show (fkSquareBoxPlanar n).G ≤
      (fkSquareBoxPlanar n).G ⊔
        (fkIsingSquareWiredDobrushinDomain n hn).wiring from le_sup_left)
  letI : Nonempty (fkSquareBoxPlanar n).V :=
    ⟨⟨fun _ => 0, by intro i; simp⟩⟩
  exact ⟨boxGraph_preconnected 2 n⟩

theorem fkIsingSquareWired_full_openCount
    (n : Nat) :
    openCount (fkSquareBoxPlanar n).G
        (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset) =
      2 * ((2 * n) * (2 * n + 1)) := by
  unfold openCount
  rw [show (fkSquareBoxPlanar n).G.edgeFinset.filter
      (fun f => FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset f = true) =
      (fkSquareBoxPlanar n).G.edgeFinset by
    ext f
    simp only [Finset.mem_filter, FK.edgeSetConfig_apply]
    tauto]
  change (StatMech.FK.boxGraph 2 n).edgeFinset.card = _
  rw [StatMech.FK.EdgeCount.boxGraph_edgeCard 2 n (by omega)]
  ring

theorem fkIsingSquareWired_empty_openCount
    (n : Nat) :
    openCount (fkSquareBoxPlanar n).G (FK.edgeSetConfig ∅) = 0 := by
  unfold openCount
  simp [FK.edgeSetConfig]


theorem fkIsingSquareWiredEulerDefect_empty_formula
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareWiredEulerDefect n hn (FK.edgeSetConfig ∅) =
      2 * ((2 * n + 1) ^ 2 - 2 * n) -
        Nat.card (fkIsingSquareWiredCompletedLoopGraph n hn
          (FK.edgeSetConfig ∅)).ConnectedComponent := by
  unfold fkIsingSquareWiredEulerDefect
  rw [fkIsingSquareWired_empty_clusterCount,
    fkIsingSquareWired_empty_openCount]
  simp only [Nat.cast_zero, add_zero]
  have hle : 2 * n ≤ (2 * n + 1) ^ 2 := by nlinarith
  rw [Nat.cast_sub hle]
  push_cast
  rfl


theorem fkIsingSquareWiredEulerDefect_full_formula
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareWiredEulerDefect n hn
        (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset) =
      2 * ((2 * n + 1) ^ 2 - 2 * n) -
        Nat.card (fkIsingSquareWiredCompletedLoopGraph n hn
          (FK.edgeSetConfig
            (fkSquareBoxPlanar n).G.edgeFinset)).ConnectedComponent := by
  unfold fkIsingSquareWiredEulerDefect
  rw [fkIsingSquareWired_full_clusterCount,
    fkIsingSquareWired_full_openCount]
  push_cast
  ring


theorem fkIsingSquareWiredEulerDefect_empty_full_iff_componentCount
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareWiredEulerDefect n hn
          (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset) =
        fkIsingSquareWiredEulerDefect n hn (FK.edgeSetConfig ∅) ↔
      Nat.card (fkIsingSquareWiredCompletedLoopGraph n hn
          (FK.edgeSetConfig
            (fkSquareBoxPlanar n).G.edgeFinset)).ConnectedComponent =
        Nat.card (fkIsingSquareWiredCompletedLoopGraph n hn
          (FK.edgeSetConfig ∅)).ConnectedComponent := by
  rw [fkIsingSquareWiredEulerDefect_full_formula,
    fkIsingSquareWiredEulerDefect_empty_formula]
  constructor
  · intro h
    have hcast :
        (Nat.card (fkIsingSquareWiredCompletedLoopGraph n hn
            (FK.edgeSetConfig
              (fkSquareBoxPlanar n).G.edgeFinset)).ConnectedComponent : Int) =
          Nat.card (fkIsingSquareWiredCompletedLoopGraph n hn
            (FK.edgeSetConfig ∅)).ConnectedComponent := by
      omega
    exact_mod_cast hcast
  · intro h
    rw [h]

end
end StatMech.Universality
