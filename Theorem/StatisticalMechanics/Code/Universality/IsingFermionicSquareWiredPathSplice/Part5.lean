/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPathSplice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion.Part19
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPathSplice.Part4
open Finset SimpleGraph


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

@[simp] theorem fkIsingSquareWiredPathSpliceCast_support
    {V : Type*} {G H : SimpleGraph V} (h : G = H)
    {u v : V} (p : G.Walk u v) :
    (fkIsingSquareWiredPathSpliceCast h p).support = p.support := by
  subst H
  rfl

theorem medialTwoEdgeSwitch_reverse_both_pairs
    {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (a b c d : V) :
    medialTwoEdgeSwitch G b a d c = medialTwoEdgeSwitch G a b c d := by
  ext u v
  simp [medialTwoEdgeSwitch, SimpleGraph.deleteEdges_adj,
    SimpleGraph.sup_adj, SimpleGraph.edge_adj, or_comm, or_left_comm,
    or_assoc]

@[simp] theorem fkIsingSquareWiredPathSpliceCast_isPath
    {V : Type*} {G H : SimpleGraph V} (h : G = H)
    {u v : V} (p : G.Walk u v) :
    (fkIsingSquareWiredPathSpliceCast h p).IsPath ↔ p.IsPath := by
  subst H
  rfl


theorem fkIsingSquareWired_double_visit_open_splice_support
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    ((fkIsingSquareWiredExplorationOrder n hn (setOpen e.1 omega) =
        (fkIsingSquareWiredExplorationOrder n hn
          (setClosed e.1 omega)).take
            ((fkIsingSquareWiredExplorationOrder n hn
              (setClosed e.1 omega)).idxOf (.dart (e, .south)) + 1) ++
          (fkIsingSquareWiredExplorationOrder n hn
            (setClosed e.1 omega)).drop
              ((fkIsingSquareWiredExplorationOrder n hn
                (setClosed e.1 omega)).idxOf (.dart (e, .east)))) ∧
      (fkIsingSquareWiredExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .west)) <
        (fkIsingSquareWiredExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .north))) ∨
    ((fkIsingSquareWiredExplorationOrder n hn (setOpen e.1 omega) =
        (fkIsingSquareWiredExplorationOrder n hn
          (setClosed e.1 omega)).take
            ((fkIsingSquareWiredExplorationOrder n hn
              (setClosed e.1 omega)).idxOf (.dart (e, .north)) + 1) ++
          (fkIsingSquareWiredExplorationOrder n hn
            (setClosed e.1 omega)).drop
              ((fkIsingSquareWiredExplorationOrder n hn
                (setClosed e.1 omega)).idxOf (.dart (e, .west)))) ∧
      (fkIsingSquareWiredExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .east)) <
        (fkIsingSquareWiredExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .south))) := by
  classical
  let S : FKIsingSquareWiredCarrier n := .dart (e, .south)
  let W : FKIsingSquareWiredCarrier n := .dart (e, .west)
  let N : FKIsingSquareWiredCarrier n := .dart (e, .north)
  let E : FKIsingSquareWiredCarrier n := .dart (e, .east)
  let G := fkIsingSquareWiredLoopGraph n hn (setClosed e.1 omega)
  let p : G.Walk (.source : FKIsingSquareWiredCarrier n) .terminal :=
    fkIsingSquareWiredExplorationPath n hn (setClosed e.1 omega)
  have hp : p.IsPath :=
    (fkIsingSquareWiredExplorationPath n hn
      (setClosed e.1 omega)).isPath
  have hSW := fkIsingSquareWired_closed_south_west_oriented_infix
    n hn omega e hwest
  have hNE := fkIsingSquareWired_closed_north_east_oriented_infix
    n hn omega e heast
  have hS : S ∈ p.support := by simpa [S, p] using hSW.mem (by simp)
  have hW : W ∈ p.support := by simpa [W, p] using hSW.mem (by simp)
  have hN : N ∈ p.support := by simpa [N, p] using hNE.mem (by simp)
  have hE : E ∈ p.support := by simpa [E, p] using hNE.mem (by simp)
  have hiSW := idxOf_succ_of_pair_infix_nodup
    (fkIsingSquareWiredExplorationOrder_nodup n hn
      (setClosed e.1 omega)) hSW
  have hiNE := idxOf_succ_of_pair_infix_nodup
    (fkIsingSquareWiredExplorationOrder_nodup n hn
      (setClosed e.1 omega)) hNE
  change p.support.idxOf W = p.support.idxOf S + 1 at hiSW
  change p.support.idxOf E = p.support.idxOf N + 1 at hiNE
  have horder := fkIsingSquareWired_double_visit_closed_order
    n hn omega e hwest heast
  change p.support.idxOf W < p.support.idxOf N ∨
    p.support.idxOf E < p.support.idxOf S at horder
  have hopenBase : fkIsingSquareWiredLoopGraph n hn (setOpen e.1 omega) =
      medialTwoEdgeSwitch G W S E N := by
    simpa [G, W, S, E, N] using
      fkIsingSquareWiredLoopGraph_setOpen_eq_twoEdgeSwitch n hn omega e
  rcases horder with hWN | hES
  · have hswitch : medialTwoEdgeSwitch G S W N E =
        medialTwoEdgeSwitch G W S E N :=
      medialTwoEdgeSwitch_reverse_both_pairs G W S E N
    have hopen : fkIsingSquareWiredLoopGraph n hn (setOpen e.1 omega) =
        medialTwoEdgeSwitch G S W N E := hopenBase.trans hswitch.symm
    obtain ⟨q, hq, hqSupport⟩ :=
      walkSplice_of_order G p hp hS hW hN hE
        (by omega) hWN (by omega)
    let qOpen : (fkIsingSquareWiredLoopGraph n hn
        (setOpen e.1 omega)).Walk
        (.source : FKIsingSquareWiredCarrier n) .terminal :=
      fkIsingSquareWiredPathSpliceCast hopen.symm q
    have hqOpen : qOpen.IsPath := by
      simpa only [qOpen, fkIsingSquareWiredPathSpliceCast_isPath] using hq
    have hcanonical : qOpen =
        (fkIsingSquareWiredExplorationPath n hn (setOpen e.1 omega) :
          (fkIsingSquareWiredLoopGraph n hn
            (setOpen e.1 omega)).Walk .source .terminal) :=
      fkIsingSquareWired_sourceTerminalPath_unique n hn
        (setOpen e.1 omega) qOpen _ hqOpen
          (fkIsingSquareWiredExplorationPath n hn
            (setOpen e.1 omega)).isPath
    left
    refine ⟨?_, by simpa only [p, W, N] using hWN⟩
    change (fkIsingSquareWiredExplorationPath n hn (setOpen e.1 omega) :
      (fkIsingSquareWiredLoopGraph n hn
        (setOpen e.1 omega)).Walk .source .terminal).support = _
    rw [← hcanonical]
    simpa only [qOpen, fkIsingSquareWiredPathSpliceCast_support,
      p, S, E] using hqSupport
  · have hswitch : medialTwoEdgeSwitch G N E S W =
        medialTwoEdgeSwitch G W S E N := by
      calc
        medialTwoEdgeSwitch G N E S W =
            medialTwoEdgeSwitch G E N W S :=
          medialTwoEdgeSwitch_reverse_both_pairs G E N W S
        _ = medialTwoEdgeSwitch G W S E N :=
          medialTwoEdgeSwitch_swap_pairs G W S E N
    have hopen : fkIsingSquareWiredLoopGraph n hn (setOpen e.1 omega) =
        medialTwoEdgeSwitch G N E S W := hopenBase.trans hswitch.symm
    obtain ⟨q, hq, hqSupport⟩ :=
      walkSplice_of_order G p hp hN hE hS hW
        (by omega) hES (by omega)
    let qOpen : (fkIsingSquareWiredLoopGraph n hn
        (setOpen e.1 omega)).Walk
        (.source : FKIsingSquareWiredCarrier n) .terminal :=
      fkIsingSquareWiredPathSpliceCast hopen.symm q
    have hqOpen : qOpen.IsPath := by
      simpa only [qOpen, fkIsingSquareWiredPathSpliceCast_isPath] using hq
    have hcanonical : qOpen =
        (fkIsingSquareWiredExplorationPath n hn (setOpen e.1 omega) :
          (fkIsingSquareWiredLoopGraph n hn
            (setOpen e.1 omega)).Walk .source .terminal) :=
      fkIsingSquareWired_sourceTerminalPath_unique n hn
        (setOpen e.1 omega) qOpen _ hqOpen
          (fkIsingSquareWiredExplorationPath n hn
            (setOpen e.1 omega)).isPath
    right
    refine ⟨?_, by simpa only [p, E, S] using hES⟩
    change (fkIsingSquareWiredExplorationPath n hn (setOpen e.1 omega) :
      (fkIsingSquareWiredLoopGraph n hn
        (setOpen e.1 omega)).Walk .source .terminal).support = _
    rw [← hcanonical]
    simpa only [qOpen, fkIsingSquareWiredPathSpliceCast_support,
      p, N, W] using hqSupport


theorem fkIsingSquareWiredLiftedWinding_eq_neg_suffix_sum
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (z : FKIsingSquareWiredCarrier n)
    (hz : z ∈ fkIsingSquareWiredExplorationOrder n hn omega) :
    fkIsingSquareWiredLiftedWinding n hn omega z =
      (-(((fkIsingSquareWiredExplorationTurnSteps n hn omega).drop
        ((fkIsingSquareWiredExplorationOrder n hn omega).idxOf z)).sum) :
          Real) * (Real.pi / 4) := by
  let p := fkIsingSquareWiredExplorationOrder n hn omega
  let t := fkIsingSquareWiredExplorationTurnSteps n hn omega
  let w : (fkIsingSquareWiredLoopGraph n hn omega).Walk
      (.source : FKIsingSquareWiredCarrier n) .terminal :=
    fkIsingSquareWiredExplorationPath n hn omega
  have hp : p = w.support := rfl
  have hpne : p ≠ [] := by
    rw [hp]
    exact w.support_ne_nil
  have hplen : 0 < p.length := List.length_pos_of_ne_nil hpne
  let lastIndex : Fin p.length := ⟨p.length - 1, by omega⟩
  have hlast : p.get lastIndex =
      (.terminal : FKIsingSquareWiredCarrier n) := by
    have hwlast := w.getLast_support
    rw [List.getLast_eq_getElem w.support_ne_nil] at hwlast
    simpa only [lastIndex, hp] using hwlast
  have hnodup : p.Nodup := by
    simpa only [p] using fkIsingSquareWiredExplorationOrder_nodup n hn omega
  have hterminalIdx : p.idxOf
      (.terminal : FKIsingSquareWiredCarrier n) = p.length - 1 := by
    have hidx := List.get_idxOf hnodup lastIndex
    rw [hlast] at hidx
    exact hidx
  have hterminal : (.terminal : FKIsingSquareWiredCarrier n) ∈ p := by
    rw [← hlast]
    exact List.get_mem p lastIndex
  have htlen : t.length = p.length - 1 := by
    simp [t, p, fkIsingSquareWiredExplorationTurnSteps]
  have htakeTerminal : t.take (p.length - 1) = t := by
    rw [← htlen, List.take_length]
  have hsum := List.sum_take_add_sum_drop t (p.idxOf z)
  have hcount :
      fkIsingSquareWiredRawTurnCount n hn omega z -
          fkIsingSquareWiredRawTurnCount n hn omega .terminal =
        -(t.drop (p.idxOf z)).sum := by
    simp only [fkIsingSquareWiredRawTurnCount, p, t]
    rw [if_pos hz, if_pos hterminal, hterminalIdx, htakeTerminal]
    rw [← hsum]
    abel
  simp only [fkIsingSquareWiredLiftedWinding,
    fkIsingSquareWiredPhysicalTurnCount]
  rw [hcount]
  push_cast
  ring


theorem fkIsingSquareWiredTransitionTurn_open_eq_closed_of_nonlocal
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (x y : FKIsingSquareWiredCarrier n)
    (hnonlocal : ∀ side,
      x = .dart (e, side) → ∀ side', y ≠ .dart (e, side')) :
    fkIsingSquareWiredTransitionTurn n hn (setOpen e.1 omega) x y =
      fkIsingSquareWiredTransitionTurn n hn (setClosed e.1 omega) x y := by
  cases x with
  | source => cases y <;> rfl
  | terminal => cases y <;> rfl
  | bond d => cases y <;> rfl
  | dart d =>
      cases y with
      | source => rfl
      | terminal => rfl
      | bond f => rfl
      | dart f =>
          rcases d with ⟨d, side⟩
          rcases f with ⟨f, side'⟩
          by_cases hd : d = e
          · subst d
            have hf : f ≠ e := by
              intro hfe
              subst f
              exact hnonlocal side rfl side' rfl
            have hopen : (f, side') ≠
                FKIsingMedialDart.localMate (setOpen e.1 omega)
                  (e, side) := by
              intro heq
              have hfirst := congrArg Prod.fst heq
              exact hf (by
                cases side <;>
                  simpa [FKIsingMedialDart.localMate] using hfirst)
            have hclosed : (f, side') ≠
                FKIsingMedialDart.localMate (setClosed e.1 omega)
                  (e, side) := by
              intro heq
              have hfirst := congrArg Prod.fst heq
              exact hf (by
                cases side <;>
                  simpa [FKIsingMedialDart.localMate] using hfirst)
            simp [fkIsingSquareWiredTransitionTurn, hopen, hclosed]
          · have hedge : d.1 ≠ e.1 := by
              intro hedge
              exact hd (Subtype.ext hedge)
            have hmate :
                FKIsingMedialDart.localMate (setOpen e.1 omega) (d, side) =
                  FKIsingMedialDart.localMate (setClosed e.1 omega)
                    (d, side) := by
              simp [FKIsingMedialDart.localMate,
                setOpen_of_ne hedge, setClosed_of_ne hedge]
            simp only [fkIsingSquareWiredTransitionTurn, hmate]

theorem wiredZipWith_eq_of_mem
    {A B C : Type*} (f g : A → B → C) (l : List A) (r : List B)
    (h : ∀ a ∈ l, ∀ b ∈ r, f a b = g a b) :
    List.zipWith f l r = List.zipWith g l r := by
  induction l generalizing r with
  | nil => rfl
  | cons a l ih =>
      cases r with
      | nil => rfl
      | cons b r =>
          simp only [List.zipWith_cons_cons]
          rw [h a (by simp) b (by simp)]
          apply congrArg (List.cons (g a b))
          exact ih r (by
            intro x hx y hy
            exact h x (by simp [hx]) y (by simp [hy]))

theorem fkIsingSquareWired_terminalSide_winding_eq_of_splice
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (d : FKIsingSquareWiredCarrier n) (prefixLength : Nat)
    (hdClosed : d ∈ fkIsingSquareWiredExplorationOrder n hn
      (setClosed e.1 omega))
    (hdOpen : d ∈ fkIsingSquareWiredExplorationOrder n hn
      (setOpen e.1 omega))
    (hprefix : prefixLength ≤
      (fkIsingSquareWiredExplorationOrder n hn
        (setClosed e.1 omega)).length)
    (hdPrefix : d ∉
      (fkIsingSquareWiredExplorationOrder n hn
        (setClosed e.1 omega)).take prefixLength)
    (hcentral : ∀ side,
      (.dart (e, side) : FKIsingSquareWiredCarrier n) ∈
        (fkIsingSquareWiredExplorationOrder n hn
          (setClosed e.1 omega)).take
            ((fkIsingSquareWiredExplorationOrder n hn
              (setClosed e.1 omega)).idxOf d + 1))
    (hsplice : fkIsingSquareWiredExplorationOrder n hn
        (setOpen e.1 omega) =
      (fkIsingSquareWiredExplorationOrder n hn
        (setClosed e.1 omega)).take prefixLength ++
      (fkIsingSquareWiredExplorationOrder n hn
        (setClosed e.1 omega)).drop
          ((fkIsingSquareWiredExplorationOrder n hn
            (setClosed e.1 omega)).idxOf d)) :
    fkIsingSquareWiredLiftedWinding n hn (setOpen e.1 omega) d =
      fkIsingSquareWiredLiftedWinding n hn (setClosed e.1 omega) d := by
  let pClosed := fkIsingSquareWiredExplorationOrder n hn
    (setClosed e.1 omega)
  let pOpen := fkIsingSquareWiredExplorationOrder n hn
    (setOpen e.1 omega)
  let tClosed := fkIsingSquareWiredExplorationTurnSteps n hn
    (setClosed e.1 omega)
  let tOpen := fkIsingSquareWiredExplorationTurnSteps n hn
    (setOpen e.1 omega)
  have hprefix' : prefixLength ≤ pClosed.length := by
    simpa only [pClosed] using hprefix
  have hdPrefix' : d ∉ pClosed.take prefixLength := by
    simpa only [pClosed] using hdPrefix
  have hcentral' (side : FKIsingMedialSide) :
      (.dart (e, side) : FKIsingSquareWiredCarrier n) ∈
        pClosed.take (pClosed.idxOf d + 1) := by
    simpa only [pClosed] using hcentral side
  have hsplice' : pOpen =
      pClosed.take prefixLength ++ pClosed.drop (pClosed.idxOf d) := by
    simpa only [pOpen, pClosed] using hsplice
  have hdlt : pClosed.idxOf d < pClosed.length :=
    List.idxOf_lt_length_iff.mpr hdClosed
  have hsuffix : pClosed.drop (pClosed.idxOf d) =
      d :: pClosed.drop (pClosed.idxOf d + 1) := by
    rw [List.drop_eq_getElem_cons hdlt, List.getElem_idxOf hdlt]
  have hprefixLength : (pClosed.take prefixLength).length = prefixLength := by
    simp only [List.length_take]
    omega
  have hidxOpen : pOpen.idxOf d = prefixLength := by
    rw [hsplice', List.idxOf_append, if_neg hdPrefix', hsuffix,
      List.idxOf_cons_self, hprefixLength]
    omega
  have hopenDrop : pOpen.drop prefixLength =
      pClosed.drop (pClosed.idxOf d) := by
    rw [hsplice']
    simpa only [hprefixLength] using
      (List.drop_left (l₁ := pClosed.take prefixLength)
        (l₂ := pClosed.drop (pClosed.idxOf d)))
  have hopenDropSucc : pOpen.drop (prefixLength + 1) =
      pClosed.drop (pClosed.idxOf d + 1) := by
    rw [← List.tail_drop, hopenDrop, List.tail_drop]
  have hclosedNodup : pClosed.Nodup := by
    simpa only [pClosed] using
      fkIsingSquareWiredExplorationOrder_nodup n hn
        (setClosed e.1 omega)
  have hsplit :
      (pClosed.take (pClosed.idxOf d + 1) ++
        pClosed.drop (pClosed.idxOf d + 1)).Nodup := by
    simpa only [List.take_append_drop] using hclosedNodup
  have hdisjoint : List.Disjoint
      (pClosed.take (pClosed.idxOf d + 1))
      (pClosed.drop (pClosed.idxOf d + 1)) := hsplit.disjoint
  have hcentralDrop (side : FKIsingMedialSide) :
      (.dart (e, side) : FKIsingSquareWiredCarrier n) ∉
        pClosed.drop (pClosed.idxOf d + 1) :=
    fun h => hdisjoint (hcentral' side) h
  have hzip :
      List.zipWith
          (fkIsingSquareWiredTransitionTurn n hn (setOpen e.1 omega))
          (pClosed.drop (pClosed.idxOf d))
          (pClosed.drop (pClosed.idxOf d + 1)) =
        List.zipWith
          (fkIsingSquareWiredTransitionTurn n hn (setClosed e.1 omega))
          (pClosed.drop (pClosed.idxOf d))
          (pClosed.drop (pClosed.idxOf d + 1)) := by
    apply wiredZipWith_eq_of_mem
    intro x hx y hy
    apply fkIsingSquareWiredTransitionTurn_open_eq_closed_of_nonlocal
    intro side _ side' hycentral
    apply hcentralDrop side'
    rw [← hycentral]
    exact hy
  have hsteps : tOpen.drop (pOpen.idxOf d) =
      tClosed.drop (pClosed.idxOf d) := by
    simp only [tOpen, tClosed, fkIsingSquareWiredExplorationTurnSteps,
      List.drop_zipWith, List.drop_tail]
    rw [hidxOpen, hopenDrop, hopenDropSucc]
    exact hzip
  rw [fkIsingSquareWiredLiftedWinding_eq_neg_suffix_sum n hn
      (setOpen e.1 omega) d hdOpen,
    fkIsingSquareWiredLiftedWinding_eq_neg_suffix_sum n hn
      (setClosed e.1 omega) d hdClosed]
  rw [hsteps]


theorem fkIsingSquareWired_double_visit_terminal_side_winding
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
      fkIsingSquareWiredLiftedWinding n hn (setOpen e.1 omega)
          (.dart (e, .east)) =
        fkIsingSquareWiredLiftedWinding n hn (setClosed e.1 omega)
          (.dart (e, .east))) ∨
    (((fkIsingSquareWiredExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .east)) <
        (fkIsingSquareWiredExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .south))) ∧
      fkIsingSquareWiredLiftedWinding n hn (setOpen e.1 omega)
          (.dart (e, .west)) =
        fkIsingSquareWiredLiftedWinding n hn (setClosed e.1 omega)
          (.dart (e, .west))) := by
  classical
  let S : FKIsingSquareWiredCarrier n := .dart (e, .south)
  let W : FKIsingSquareWiredCarrier n := .dart (e, .west)
  let N : FKIsingSquareWiredCarrier n := .dart (e, .north)
  let E : FKIsingSquareWiredCarrier n := .dart (e, .east)
  let pClosed := fkIsingSquareWiredExplorationOrder n hn
    (setClosed e.1 omega)
  let pOpen := fkIsingSquareWiredExplorationOrder n hn
    (setOpen e.1 omega)
  have hSW := fkIsingSquareWired_closed_south_west_oriented_infix
    n hn omega e hwest
  have hNE := fkIsingSquareWired_closed_north_east_oriented_infix
    n hn omega e heast
  have hS : S ∈ pClosed := by simpa [S, pClosed] using hSW.mem (by simp)
  have hW : W ∈ pClosed := by simpa [W, pClosed] using hSW.mem (by simp)
  have hN : N ∈ pClosed := by simpa [N, pClosed] using hNE.mem (by simp)
  have hE : E ∈ pClosed := by simpa [E, pClosed] using hNE.mem (by simp)
  have hiSW := idxOf_succ_of_pair_infix_nodup
    (fkIsingSquareWiredExplorationOrder_nodup n hn
      (setClosed e.1 omega)) hSW
  have hiNE := idxOf_succ_of_pair_infix_nodup
    (fkIsingSquareWiredExplorationOrder_nodup n hn
      (setClosed e.1 omega)) hNE
  change pClosed.idxOf W = pClosed.idxOf S + 1 at hiSW
  change pClosed.idxOf E = pClosed.idxOf N + 1 at hiNE
  rcases fkIsingSquareWired_double_visit_open_splice_support
      n hn omega e hwest heast with
    ⟨hsplice, hWN⟩ | ⟨hsplice, hES⟩
  · left
    refine ⟨hWN, ?_⟩
    have hsplice' : pOpen =
        pClosed.take (pClosed.idxOf S + 1) ++
          pClosed.drop (pClosed.idxOf E) := by
      simpa only [pOpen, pClosed, S, E] using hsplice
    have hWN' : pClosed.idxOf W < pClosed.idxOf N := by
      simpa only [pClosed, W, N] using hWN
    have hprefix : pClosed.idxOf S + 1 ≤ pClosed.length := by
      have := List.idxOf_lt_length_iff.mpr hS
      omega
    have hEPrefix : E ∉ pClosed.take (pClosed.idxOf S + 1) := by
      rw [List.mem_take_iff_idxOf_lt hE]
      omega
    have hcentral (side : FKIsingMedialSide) :
        (.dart (e, side) : FKIsingSquareWiredCarrier n) ∈
          pClosed.take (pClosed.idxOf E + 1) := by
      cases side
      · exact (List.mem_take_iff_idxOf_lt hW).2 (by omega)
      · exact (List.mem_take_iff_idxOf_lt hE).2 (by omega)
      · exact (List.mem_take_iff_idxOf_lt hS).2 (by omega)
      · exact (List.mem_take_iff_idxOf_lt hN).2 (by omega)
    have hEOpen : E ∈ pOpen := by
      rw [hsplice', List.mem_append]
      right
      rw [List.drop_eq_getElem_cons
        (List.idxOf_lt_length_iff.mpr hE),
        List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hE)]
      simp
    have hwind := fkIsingSquareWired_terminalSide_winding_eq_of_splice
      n hn omega e E (pClosed.idxOf S + 1) hE hEOpen
        hprefix hEPrefix hcentral hsplice
    simpa only [E] using hwind
  · right
    refine ⟨hES, ?_⟩
    have hsplice' : pOpen =
        pClosed.take (pClosed.idxOf N + 1) ++
          pClosed.drop (pClosed.idxOf W) := by
      simpa only [pOpen, pClosed, N, W] using hsplice
    have hES' : pClosed.idxOf E < pClosed.idxOf S := by
      simpa only [pClosed, E, S] using hES
    have hprefix : pClosed.idxOf N + 1 ≤ pClosed.length := by
      have := List.idxOf_lt_length_iff.mpr hN
      omega
    have hWPrefix : W ∉ pClosed.take (pClosed.idxOf N + 1) := by
      rw [List.mem_take_iff_idxOf_lt hW]
      omega
    have hcentral (side : FKIsingMedialSide) :
        (.dart (e, side) : FKIsingSquareWiredCarrier n) ∈
          pClosed.take (pClosed.idxOf W + 1) := by
      cases side
      · exact (List.mem_take_iff_idxOf_lt hW).2 (by omega)
      · exact (List.mem_take_iff_idxOf_lt hE).2 (by omega)
      · exact (List.mem_take_iff_idxOf_lt hS).2 (by omega)
      · exact (List.mem_take_iff_idxOf_lt hN).2 (by omega)
    have hWOpen : W ∈ pOpen := by
      rw [hsplice', List.mem_append]
      right
      rw [List.drop_eq_getElem_cons
        (List.idxOf_lt_length_iff.mpr hW),
        List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hW)]
      simp
    have hwind := fkIsingSquareWired_terminalSide_winding_eq_of_splice
      n hn omega e W (pClosed.idxOf N + 1) hW hWOpen
        hprefix hWPrefix hcentral hsplice
    simpa only [W] using hwind


theorem fkIsingSquareWired_double_visit_terminal_side_phase
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
          (setOpen e.1 omega) (.dart (e, .east)) =
        (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
          (setClosed e.1 omega) (.dart (e, .east))) ∨
    (((fkIsingSquareWiredExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .east)) <
        (fkIsingSquareWiredExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .south))) ∧
      (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
          (setOpen e.1 omega) (.dart (e, .west)) =
        (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
          (setClosed e.1 omega) (.dart (e, .west))) := by
  rcases fkIsingSquareWired_double_visit_terminal_side_winding
      n hn omega e hwest heast with ⟨horder, hwind⟩ | ⟨horder, hwind⟩
  · left
    refine ⟨horder, ?_⟩
    unfold FKIsingDobrushinDomain.windingPhase
    simpa only [fkIsingSquareWiredDobrushinDomain, hwind]
  · right
    refine ⟨horder, ?_⟩
    unfold FKIsingDobrushinDomain.windingPhase
    simpa only [fkIsingSquareWiredDobrushinDomain, hwind]

end
end StatMech.Universality
