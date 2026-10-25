/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIntegratedPrimitive.Part5


namespace StatMech.Universality

open Finset Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareWired_terminalBond_mem_explorationOrder
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    (.bond (fkIsingSquareWiredTerminalDart n hn) :
        FKIsingSquareWiredCarrier n) ∈
      fkIsingSquareWiredExplorationOrder n hn omega := by
  have hadj : (fkIsingSquareWiredLoopGraph n hn omega).Adj
      (.terminal : FKIsingSquareWiredCarrier n)
      (.bond (fkIsingSquareWiredTerminalDart n hn)) := by
    simp
  have hedge := fkIsingSquareWiredExplorationPath_mem_edges_of_adj
    n hn omega (fkIsingSquareWiredExplorationOrder_terminal_mem n hn omega)
      hadj
  have hinfix := Walk.infix_support_iff_mem_edges.mpr hedge
  rcases hinfix with h | h
  · exact h.mem (by simp)
  · exact h.mem (by simp)

theorem fkIsingSquareWired_terminalBond_rawTurnCount
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    fkIsingSquareWiredRawTurnCount n hn omega
        (.bond (fkIsingSquareWiredTerminalDart n hn)) =
      fkIsingSquareWiredRawTurnCount n hn omega .terminal := by
  let p := fkIsingSquareWiredExplorationOrder n hn omega
  let x : FKIsingSquareWiredCarrier n := .terminal
  let y : FKIsingSquareWiredCarrier n :=
    .bond (fkIsingSquareWiredTerminalDart n hn)
  have hadj : (fkIsingSquareWiredLoopGraph n hn omega).Adj x y := by
    simp [x, y]
  have hxy := Walk.infix_support_iff_mem_edges.mpr
    (fkIsingSquareWiredExplorationPath_mem_edges_of_adj n hn omega
      (fkIsingSquareWiredExplorationOrder_terminal_mem n hn omega) hadj)
  have hx : x ∈ p := by simp [x, p]
  have hy : y ∈ p := by
    simpa [y, p] using
      fkIsingSquareWired_terminalBond_mem_explorationOrder n hn omega
  have hix : p.idxOf x < p.length := List.idxOf_lt_length_iff.mpr hx
  have hiy : p.idxOf y < p.length := List.idxOf_lt_length_iff.mpr hy
  rcases hxy with hf | hb
  · have hi := idxOf_succ_of_pair_infix_nodup
        (fkIsingSquareWiredExplorationOrder_nodup n hn omega) hf
    have hs := fkIsingSquareWiredRawTurnCount_succ n hn omega (p.idxOf x)
      (by rw [← hi]; exact hiy)
    simpa only [p, x, y, List.getElem_idxOf hix,
      ← hi, List.getElem_idxOf hiy, fkIsingSquareWiredTransitionTurn,
      add_zero] using hs
  · have hi := idxOf_succ_of_pair_infix_nodup
        (fkIsingSquareWiredExplorationOrder_nodup n hn omega) hb
    have hs := fkIsingSquareWiredRawTurnCount_succ n hn omega (p.idxOf y)
      (by rw [← hi]; exact hix)
    have hs' : fkIsingSquareWiredRawTurnCount n hn omega .terminal =
        fkIsingSquareWiredRawTurnCount n hn omega
          (.bond (fkIsingSquareWiredTerminalDart n hn)) := by
      simpa only [p, x, y, List.getElem_idxOf hiy,
        ← hi, List.getElem_idxOf hix, fkIsingSquareWiredTransitionTurn,
        add_zero] using hs
    exact hs'.symm

theorem fkIsingSquareWired_terminalBond_observable
    (n : Nat) (hn : 0 < n) :
    (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
        (.bond (fkIsingSquareWiredTerminalDart n hn)) = 1 := by
  rw [← fkIsingSquareWired_fermionicObservable_terminal n hn]
  unfold FKIsingDobrushinDomain.fermionicObservable
  apply Finset.sum_congr rfl
  intro omega _
  have hbmem : (.bond (fkIsingSquareWiredTerminalDart n hn) :
      FKIsingSquareWiredCarrier n) ∈
      fkIsingSquareWiredExplorationTrace n hn omega := by
    rw [mem_fkIsingSquareWiredExplorationTrace_iff]
    exact (fkIsingSquareWiredLoopGraph_source_reachable_terminal n hn omega).trans
      (show (fkIsingSquareWiredLoopGraph n hn omega).Adj
        (.terminal : FKIsingSquareWiredCarrier n)
        (.bond (fkIsingSquareWiredTerminalDart n hn)) by simp).reachable
  have htmem : (.terminal : FKIsingSquareWiredCarrier n) ∈
      fkIsingSquareWiredExplorationTrace n hn omega := by
    rw [mem_fkIsingSquareWiredExplorationTrace_iff]
    exact fkIsingSquareWiredLoopGraph_source_reachable_terminal n hn omega
  simp only [FKIsingDobrushinDomain.fermionicSummand,
    fkIsingSquareWiredDobrushinDomain, hbmem, htmem, if_true,
    FKIsingDobrushinDomain.windingPhase]
  rw [show fkIsingSquareWiredLiftedWinding n hn omega
        (.bond (fkIsingSquareWiredTerminalDart n hn)) = 0 by
    unfold fkIsingSquareWiredLiftedWinding
      fkIsingSquareWiredPhysicalTurnCount
    rw [fkIsingSquareWired_terminalBond_rawTurnCount n hn omega]
    norm_num]
  simp

theorem fkIsingSquareWired_terminalDart_observable
    (n : Nat) (hn : 0 < n) :
    (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquareWiredTerminalDart n hn)) = 1 := by
  rw [← fkIsingSquareWired_fermionicObservable_incidence]
  exact fkIsingSquareWired_terminalBond_observable n hn

theorem fkIsingSquareWired_terminalDart_increment
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareWiredPrimitiveIncrement n hn
        (.dart (fkIsingSquareWiredTerminalDart n hn)) = 1 := by
  unfold fkIsingSquareWiredPrimitiveIncrement isingPrimitiveIncrement
  rw [fkIsingSquareWired_terminalDart_observable n hn]
  norm_num

namespace FKIsingSquareFullIntegratedPrimitive

theorem vertex_eq_of_common_face_increment_eq
    (n : Nat) (hn : 0 < n)
    (e f : FKIsingSquareInteriorRadialIncidence n hn)
    (hface : fkIsingSquareFullFaceOfRadialIncidence n hn e =
      fkIsingSquareFullFaceOfRadialIncidence n hn f)
    (hinc : fkIsingSquareInteriorRadialIncrement n hn e =
      fkIsingSquareInteriorRadialIncrement n hn f) :
    vertexPrimitive n hn (fkIsingSquareInteriorRadialEndpoint n hn e) =
      vertexPrimitive n hn
        (fkIsingSquareInteriorRadialEndpoint n hn f) := by
  have he := face_sub_vertex n hn e
  have hf := face_sub_vertex n hn f
  rw [hface] at he
  linarith

theorem face_eq_of_common_vertex_increment_eq
    (n : Nat) (hn : 0 < n)
    (e f : FKIsingSquareInteriorRadialIncidence n hn)
    (hvertex : fkIsingSquareInteriorRadialEndpoint n hn e =
      fkIsingSquareInteriorRadialEndpoint n hn f)
    (hinc : fkIsingSquareInteriorRadialIncrement n hn e =
      fkIsingSquareInteriorRadialIncrement n hn f) :
    facePrimitive n hn (fkIsingSquareFullFaceOfRadialIncidence n hn e) =
      facePrimitive n hn
        (fkIsingSquareFullFaceOfRadialIncidence n hn f) := by
  have he := face_sub_vertex n hn e
  have hf := face_sub_vertex n hn f
  rw [hvertex] at he
  linarith

end FKIsingSquareFullIntegratedPrimitive
end
end StatMech.Universality
