/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPathSplice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion.Part19
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPathSplice.Part3
open Finset SimpleGraph


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareWiredLoopGraph_adj_oddClass
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y : FKIsingSquareWiredCarrier n}
    (hxy : (fkIsingSquareWiredLoopGraph n hn omega).Adj x y) :
    fkIsingSquareWiredCarrierOddClass n x ↔
      ¬ fkIsingSquareWiredCarrierOddClass n y := by
  rcases hxy with hinc | htrans
  · rcases hinc with ⟨hxs, hxt, rfl⟩
    cases x with
    | source => exact False.elim (hxs rfl)
    | terminal => exact False.elim (hxt rfl)
    | dart d =>
        cases hcorner : (fkIsingSquareSideCorner d.2).2 <;>
          simp [fkIsingSquareWiredCarrierOddClass,
            fkIsingSquareWiredIncidenceMate, hcorner]
    | bond d =>
        cases hcorner : (fkIsingSquareSideCorner d.2).2 <;>
          simp [fkIsingSquareWiredCarrierOddClass,
            fkIsingSquareWiredIncidenceMate, hcorner]
  · subst y
    cases x with
    | source =>
        simp [fkIsingSquareWiredCarrierOddClass,
          fkIsingSquareWiredTransitionMate,
          fkIsingSquareWiredSourceDart,
          fkIsingSquareWiredBoundaryDart]
    | terminal =>
        simp [fkIsingSquareWiredCarrierOddClass,
          fkIsingSquareWiredTransitionMate,
          fkIsingSquareWiredTerminalDart,
          fkIsingSquareWiredBoundaryDart]
    | dart d =>
        have hne := fkIsingSquare_localMate_cornerTurn_ne n omega d
        cases hd : (fkIsingSquareSideCorner d.2).2 <;>
          cases hm : (fkIsingSquareSideCorner
            (FKIsingMedialDart.localMate omega d).2).2 <;>
          simp_all [fkIsingSquareWiredCarrierOddClass,
            fkIsingSquareWiredTransitionMate]
    | bond d =>
        by_cases hs : d = fkIsingSquareWiredSourceDart n hn
        · subst d
          simp [fkIsingSquareWiredCarrierOddClass,
            fkIsingSquareWiredTransitionMate,
            fkIsingSquareWiredSourceDart,
            fkIsingSquareWiredBoundaryDart]
        by_cases ht : d = fkIsingSquareWiredTerminalDart n hn
        · subst d
          simp only [fkIsingSquareWiredTransitionMate]
          rw [if_neg hs]
          simp [fkIsingSquareWiredCarrierOddClass,
            fkIsingSquareWiredTerminalDart,
            fkIsingSquareWiredBoundaryDart]
        · have hne := fkIsingSquareWiredBondMate_cornerTurn_ne n hn d
          cases hd : (fkIsingSquareSideCorner d.2).2 <;>
            cases hm : (fkIsingSquareSideCorner
              (fkIsingSquareWiredBondMate n hn d).2).2 <;>
            simp_all [fkIsingSquareWiredCarrierOddClass,
              fkIsingSquareWiredTransitionMate, hs, ht]

theorem fkIsingSquareWiredExplorationPath_oddClass
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (i : Nat)
    (hi : i ≤ (fkIsingSquareWiredExplorationPath n hn omega :
      (fkIsingSquareWiredLoopGraph n hn omega).Walk .source .terminal).length) :
    fkIsingSquareWiredCarrierOddClass n
        ((fkIsingSquareWiredExplorationPath n hn omega :
          (fkIsingSquareWiredLoopGraph n hn omega).Walk
            .source .terminal).getVert i) ↔
      Odd i := by
  let p : (fkIsingSquareWiredLoopGraph n hn omega).Walk
      (.source : FKIsingSquareWiredCarrier n) .terminal :=
    fkIsingSquareWiredExplorationPath n hn omega
  change fkIsingSquareWiredCarrierOddClass n (p.getVert i) ↔ Odd i
  induction i with
  | zero => simp [p, fkIsingSquareWiredCarrierOddClass]
  | succ i ih =>
      have hi0 : i < p.length := by simpa [p] using hi
      have hadj := p.adj_getVert_succ hi0
      have hflip := fkIsingSquareWiredLoopGraph_adj_oddClass
        n hn omega hadj
      have ih' := ih (by simpa [p] using Nat.le_of_lt hi0)
      have hrev : fkIsingSquareWiredCarrierOddClass n (p.getVert (i + 1)) ↔
          ¬ fkIsingSquareWiredCarrierOddClass n (p.getVert i) := by
        tauto
      rw [hrev, ih', Nat.odd_add_one]


theorem fkIsingSquareWired_localMate_infix_of_counterclockwise
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (side : FKIsingMedialSide)
    (hccw : (fkIsingSquareSideCorner side).2 = .counterclockwise)
    (h : fkIsingSquareWiredPathUsesLocalSide n hn omega e side) :
    [(.dart (FKIsingMedialDart.localMate omega (e, side)) :
        FKIsingSquareWiredCarrier n), .dart (e, side)] <:+:
      fkIsingSquareWiredExplorationOrder n hn omega := by
  let H := fkIsingSquareWiredLoopGraph n hn omega
  let M := fkIsingSquareWiredIncidenceGraph n
  let p : H.Walk (.source : FKIsingSquareWiredCarrier n) .terminal :=
    fkIsingSquareWiredExplorationPath n hn omega
  let x : FKIsingSquareWiredCarrier n := .dart (e, side)
  let y : FKIsingSquareWiredCarrier n :=
    .dart (FKIsingMedialDart.localMate omega (e, side))
  rcases fkIsingSquareWired_localMate_infix_explorationOrder
      n hn omega e side h with hforward | hbackward
  · exfalso
    have hx : x ∈ p.support := hforward.mem (by simp [x])
    have hy : y ∈ p.support := hforward.mem (by simp [y])
    have hidx := idxOf_succ_of_pair_infix_nodup
      (fkIsingSquareWiredExplorationOrder_nodup n hn omega) hforward
    change p.support.idxOf y = p.support.idxOf x + 1 at hidx
    have hilt : p.support.idxOf x < p.length := by
      have hylt : p.support.idxOf y < p.support.length :=
        List.idxOf_lt_length_iff.mpr hy
      rw [p.length_support, hidx] at hylt
      omega
    have hgetx : p.getVert (p.support.idxOf x) = x :=
      p.getVert_support_idxOf hx
    have hgety : p.getVert (p.support.idxOf x + 1) = y := by
      have hy' := p.getVert_support_idxOf hy
      rw [hidx] at hy'
      exact hy'
    have hfirst : ¬ M.Adj (p.getVert 0) (p.getVert 1) := by
      intro hinc
      rcases hinc with ⟨hsource, _, _⟩
      simpa [p] using hsource
    have hincIff :=
      isAlternating_path_edge_iff_odd
        (fkIsingSquareWiredLoopGraph_isAlternating_incidence n hn omega)
        p (fkIsingSquareWiredExplorationPath n hn omega).isPath hfirst
        (p.support.idxOf x) hilt
    have hnotinc : ¬ M.Adj
        (p.getVert (p.support.idxOf x))
        (p.getVert (p.support.idxOf x + 1)) := by
      rw [hgetx, hgety]
      dsimp only [M, x, y]
      simp only [fkIsingSquareWiredIncidenceGraph]
      simp [fkIsingSquareWiredIncidenceMate]
    have hnotodd : ¬ Odd (p.support.idxOf x) := fun hodd =>
      hnotinc (hincIff.mpr hodd)
    have hclass : fkIsingSquareWiredCarrierOddClass n x ↔
        Odd (p.support.idxOf x) := by
      have hpath := fkIsingSquareWiredExplorationPath_oddClass n hn omega
        (p.support.idxOf x) (Nat.le_of_lt hilt)
      change fkIsingSquareWiredCarrierOddClass n
        (p.getVert (p.support.idxOf x)) ↔ Odd (p.support.idxOf x) at hpath
      rw [hgetx] at hpath
      exact hpath
    have hxclass : fkIsingSquareWiredCarrierOddClass n x := by
      simpa [x, fkIsingSquareWiredCarrierOddClass] using hccw
    exact hnotodd (hclass.mp hxclass)
  · exact hbackward

theorem fkIsingSquareWired_closed_south_west_oriented_infix
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west) :
    [(.dart (e, .south) : FKIsingSquareWiredCarrier n), .dart (e, .west)] <:+:
      fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega) := by
  simpa [FKIsingMedialDart.localMate, setClosed_self] using
    fkIsingSquareWired_localMate_infix_of_counterclockwise n hn
      (setClosed e.1 omega) e .west rfl h

theorem fkIsingSquareWired_closed_north_east_oriented_infix
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    [(.dart (e, .north) : FKIsingSquareWiredCarrier n), .dart (e, .east)] <:+:
      fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega) := by
  simpa [FKIsingMedialDart.localMate, setClosed_self,
    fkIsingSquareSideCorner] using
    fkIsingSquareWired_localMate_infix_of_counterclockwise n hn
      (setClosed e.1 omega) e .east rfl h

theorem fkIsingSquareWired_open_north_west_oriented_infix
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquareWiredPathUsesLocalSide n hn
      (setOpen e.1 omega) e .west) :
    [(.dart (e, .north) : FKIsingSquareWiredCarrier n), .dart (e, .west)] <:+:
      fkIsingSquareWiredExplorationOrder n hn (setOpen e.1 omega) := by
  simpa [FKIsingMedialDart.localMate, setOpen_self] using
    fkIsingSquareWired_localMate_infix_of_counterclockwise n hn
      (setOpen e.1 omega) e .west rfl h

theorem fkIsingSquareWired_open_south_east_oriented_infix
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquareWiredPathUsesLocalSide n hn
      (setOpen e.1 omega) e .east) :
    [(.dart (e, .south) : FKIsingSquareWiredCarrier n), .dart (e, .east)] <:+:
      fkIsingSquareWiredExplorationOrder n hn (setOpen e.1 omega) := by
  simpa [FKIsingMedialDart.localMate, setOpen_self,
    fkIsingSquareSideCorner] using
    fkIsingSquareWired_localMate_infix_of_counterclockwise n hn
      (setOpen e.1 omega) e .east rfl h


theorem fkIsingSquareWired_double_visit_closed_order
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    (fkIsingSquareWiredExplorationOrder n hn
        (setClosed e.1 omega)).idxOf (.dart (e, .west)) <
      (fkIsingSquareWiredExplorationOrder n hn
        (setClosed e.1 omega)).idxOf (.dart (e, .north)) ∨
    (fkIsingSquareWiredExplorationOrder n hn
        (setClosed e.1 omega)).idxOf (.dart (e, .east)) <
      (fkIsingSquareWiredExplorationOrder n hn
        (setClosed e.1 omega)).idxOf (.dart (e, .south)) := by
  let p := fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)
  have hSW := fkIsingSquareWired_closed_south_west_oriented_infix
    n hn omega e hwest
  have hNE := fkIsingSquareWired_closed_north_east_oriented_infix
    n hn omega e heast
  have hiSW := idxOf_succ_of_pair_infix_nodup
    (fkIsingSquareWiredExplorationOrder_nodup n hn
      (setClosed e.1 omega)) hSW
  have hiNE := idxOf_succ_of_pair_infix_nodup
    (fkIsingSquareWiredExplorationOrder_nodup n hn
      (setClosed e.1 omega)) hNE
  have hS : (.dart (e, .south) : FKIsingSquareWiredCarrier n) ∈ p :=
    hSW.mem (by simp)
  have hW : (.dart (e, .west) : FKIsingSquareWiredCarrier n) ∈ p :=
    hSW.mem (by simp)
  have hN : (.dart (e, .north) : FKIsingSquareWiredCarrier n) ∈ p :=
    hNE.mem (by simp)
  have hE : (.dart (e, .east) : FKIsingSquareWiredCarrier n) ∈ p :=
    hNE.mem (by simp)
  have hSN : p.idxOf (.dart (e, .south)) ≠
      p.idxOf (.dart (e, .north)) := by
    intro hi
    have heq := (List.idxOf_inj hS).mp hi
    simp at heq
  have hWN : p.idxOf (.dart (e, .west)) ≠
      p.idxOf (.dart (e, .north)) := by
    intro hi
    have heq := (List.idxOf_inj hW).mp hi
    simp at heq
  have hES : p.idxOf (.dart (e, .east)) ≠
      p.idxOf (.dart (e, .south)) := by
    intro hi
    have heq := (List.idxOf_inj hE).mp hi
    simp at heq
  change p.idxOf (.dart (e, .west)) < p.idxOf (.dart (e, .north)) ∨
    p.idxOf (.dart (e, .east)) < p.idxOf (.dart (e, .south))
  change p.idxOf (.dart (e, .west)) =
    p.idxOf (.dart (e, .south)) + 1 at hiSW
  change p.idxOf (.dart (e, .east)) =
    p.idxOf (.dart (e, .north)) + 1 at hiNE
  omega

end
end StatMech.Universality
