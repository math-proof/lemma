/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part39
import Mathlib.Logic.Equiv.Fintype
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion.Part17


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareWiredRawTurnCount_succ
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (i : Nat)
    (hi : i + 1 < (fkIsingSquareWiredExplorationOrder n hn omega).length) :
    fkIsingSquareWiredRawTurnCount n hn omega
        (fkIsingSquareWiredExplorationOrder n hn omega)[i + 1] =
      fkIsingSquareWiredRawTurnCount n hn omega
        (fkIsingSquareWiredExplorationOrder n hn omega)[i] +
      fkIsingSquareWiredTransitionTurn n hn omega
        (fkIsingSquareWiredExplorationOrder n hn omega)[i]
        (fkIsingSquareWiredExplorationOrder n hn omega)[i + 1] := by
  let p := fkIsingSquareWiredExplorationOrder n hn omega
  let t := fkIsingSquareWiredExplorationTurnSteps n hn omega
  have hi' : i + 1 < p.length := by simpa [p] using hi
  have hi0 : i < p.length := by omega
  have hmem0 : p[i] ∈ p := List.getElem_mem _
  have hmem1 : p[i + 1] ∈ p := List.getElem_mem _
  have hnodup : p.Nodup := by
    simpa [p] using fkIsingSquareWiredExplorationOrder_nodup n hn omega
  have hidx0 : p.idxOf p[i] = i := List.get_idxOf hnodup ⟨i, hi0⟩
  have hidx1 : p.idxOf p[i + 1] = i + 1 :=
    List.get_idxOf hnodup ⟨i + 1, hi'⟩
  have htlen : i < t.length := by
    simp [t, fkIsingSquareWiredExplorationTurnSteps]
    omega
  have htget :
      t[i] = fkIsingSquareWiredTransitionTurn n hn omega p[i] p[i + 1] := by
    simp [t, fkIsingSquareWiredExplorationTurnSteps, p]
  change (if p[i + 1] ∈ p then
      (t.take (p.idxOf p[i + 1])).sum else 0) = _
  rw [if_pos hmem1]
  change _ = (if p[i] ∈ p then
      (t.take (p.idxOf p[i])).sum else 0) + _
  rw [if_pos hmem0, hidx0, hidx1,
    List.sum_take_succ t i htlen, htget]

theorem fkIsingSquareWiredRawTurnCount_localMate
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (side : FKIsingMedialSide)
    (h : fkIsingSquareWiredPathUsesLocalSide n hn omega e side) :
    (fkIsingSquareWiredRawTurnCount n hn omega
        (.dart (FKIsingMedialDart.localMate omega (e, side))) =
      fkIsingSquareWiredRawTurnCount n hn omega (.dart (e, side)) +
        fkIsingSquareWiredTransitionTurn n hn omega
          (.dart (e, side))
          (.dart (FKIsingMedialDart.localMate omega (e, side)))) ∨
    (fkIsingSquareWiredRawTurnCount n hn omega (.dart (e, side)) =
      fkIsingSquareWiredRawTurnCount n hn omega
        (.dart (FKIsingMedialDart.localMate omega (e, side))) +
        fkIsingSquareWiredTransitionTurn n hn omega
          (.dart (FKIsingMedialDart.localMate omega (e, side)))
          (.dart (e, side))) := by
  let p := fkIsingSquareWiredExplorationOrder n hn omega
  let x : FKIsingSquareWiredCarrier n := .dart (e, side)
  let y : FKIsingSquareWiredCarrier n :=
    .dart (FKIsingMedialDart.localMate omega (e, side))
  have hxy := fkIsingSquareWired_localMate_infix_explorationOrder
    n hn omega e side h
  have hx : x ∈ p := by simpa [x, p] using h
  have hy : y ∈ p := hxy.elim
    (fun hf => hf.mem (by simp [y]))
    (fun hb => hb.mem (by simp [y]))
  have hix : p.idxOf x < p.length := List.idxOf_lt_length_iff.mpr hx
  have hiy : p.idxOf y < p.length := List.idxOf_lt_length_iff.mpr hy
  rcases hxy with hf | hb
  · have hi := idxOf_succ_of_pair_infix_nodup
        (fkIsingSquareWiredExplorationOrder_nodup n hn omega) hf
    have hs := fkIsingSquareWiredRawTurnCount_succ n hn omega (p.idxOf x)
      (by rw [← hi]; exact hiy)
    left
    simpa only [p, x, y, List.getElem_idxOf hix,
      ← hi, List.getElem_idxOf hiy] using hs
  · have hi := idxOf_succ_of_pair_infix_nodup
        (fkIsingSquareWiredExplorationOrder_nodup n hn omega) hb
    have hs := fkIsingSquareWiredRawTurnCount_succ n hn omega (p.idxOf y)
      (by rw [← hi]; exact hix)
    right
    simpa only [p, x, y, List.getElem_idxOf hiy,
      ← hi, List.getElem_idxOf hix] using hs

theorem fkIsingSquareWired_closed_west_south_rawTurnCount
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west) :
    fkIsingSquareWiredRawTurnCount n hn (setClosed e.1 omega)
        (.dart (e, .south)) =
      fkIsingSquareWiredRawTurnCount n hn (setClosed e.1 omega)
        (.dart (e, .west)) - 2 := by
  have hm := fkIsingSquareWiredRawTurnCount_localMate
    n hn (setClosed e.1 omega) e .west h
  rcases fkIsingSquareWiredTransitionTurn_local_table n hn omega e with
    ⟨hWS, hSW, _hEN, _hNE, _hWN, _hNW, _hES, _hSE⟩
  simp only [FKIsingMedialDart.localMate, setClosed_self] at hm
  rw [hWS, hSW] at hm
  omega

theorem fkIsingSquareWired_closed_east_north_rawTurnCount
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    fkIsingSquareWiredRawTurnCount n hn (setClosed e.1 omega)
        (.dart (e, .north)) =
      fkIsingSquareWiredRawTurnCount n hn (setClosed e.1 omega)
        (.dart (e, .east)) - 2 := by
  have hm := fkIsingSquareWiredRawTurnCount_localMate
    n hn (setClosed e.1 omega) e .east h
  rcases fkIsingSquareWiredTransitionTurn_local_table n hn omega e with
    ⟨_hWS, _hSW, hEN, hNE, _hWN, _hNW, _hES, _hSE⟩
  simp only [FKIsingMedialDart.localMate, setClosed_self] at hm
  rw [hEN, hNE] at hm
  omega

theorem fkIsingSquareWired_open_west_north_rawTurnCount
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquareWiredPathUsesLocalSide n hn
      (setOpen e.1 omega) e .west) :
    fkIsingSquareWiredRawTurnCount n hn (setOpen e.1 omega)
        (.dart (e, .north)) =
      fkIsingSquareWiredRawTurnCount n hn (setOpen e.1 omega)
        (.dart (e, .west)) + 2 := by
  have hm := fkIsingSquareWiredRawTurnCount_localMate
    n hn (setOpen e.1 omega) e .west h
  rcases fkIsingSquareWiredTransitionTurn_local_table n hn omega e with
    ⟨_hWS, _hSW, _hEN, _hNE, hWN, hNW, _hES, _hSE⟩
  simp only [FKIsingMedialDart.localMate, setOpen_self] at hm
  rw [hWN, hNW] at hm
  omega

theorem fkIsingSquareWired_open_east_south_rawTurnCount
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquareWiredPathUsesLocalSide n hn
      (setOpen e.1 omega) e .east) :
    fkIsingSquareWiredRawTurnCount n hn (setOpen e.1 omega)
        (.dart (e, .south)) =
      fkIsingSquareWiredRawTurnCount n hn (setOpen e.1 omega)
        (.dart (e, .east)) + 2 := by
  have hm := fkIsingSquareWiredRawTurnCount_localMate
    n hn (setOpen e.1 omega) e .east h
  rcases fkIsingSquareWiredTransitionTurn_local_table n hn omega e with
    ⟨_hWS, _hSW, _hEN, _hNE, _hWN, _hNW, hES, hSE⟩
  simp only [FKIsingMedialDart.localMate, setOpen_self] at hm
  rw [hES, hSE] at hm
  omega

end
end StatMech.Universality
