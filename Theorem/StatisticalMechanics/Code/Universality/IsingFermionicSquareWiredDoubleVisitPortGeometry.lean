/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredDoubleVisitPortGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part34
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredOpenFibers


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareWired_double_visit_open_pair_exact
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    (fkIsingSquareWiredPathUsesLocalSide n hn
        (setOpen e.1 omega) e .west ∧
      fkIsingSquareWiredPathUsesLocalSide n hn
        (setOpen e.1 omega) e .north ∧
      ¬fkIsingSquareWiredPathUsesLocalSide n hn
        (setOpen e.1 omega) e .east ∧
      ¬fkIsingSquareWiredPathUsesLocalSide n hn
        (setOpen e.1 omega) e .south) ∨
    (¬fkIsingSquareWiredPathUsesLocalSide n hn
        (setOpen e.1 omega) e .west ∧
      ¬fkIsingSquareWiredPathUsesLocalSide n hn
        (setOpen e.1 omega) e .north ∧
      fkIsingSquareWiredPathUsesLocalSide n hn
        (setOpen e.1 omega) e .east ∧
      fkIsingSquareWiredPathUsesLocalSide n hn
        (setOpen e.1 omega) e .south) := by
  classical
  let W : FKIsingSquareWiredCarrier n := .dart (e, .west)
  let E : FKIsingSquareWiredCarrier n := .dart (e, .east)
  let S : FKIsingSquareWiredCarrier n := .dart (e, .south)
  let N : FKIsingSquareWiredCarrier n := .dart (e, .north)
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
  have hnodup : pClosed.Nodup :=
    fkIsingSquareWiredExplorationOrder_nodup n hn (setClosed e.1 omega)
  rcases fkIsingSquareWired_double_visit_open_splice_support
      n hn omega e hwest heast with
    ⟨hsplice, hWN⟩ | ⟨hsplice, hES⟩
  · right
    have hWN' : pClosed.idxOf W < pClosed.idxOf N := by
      simpa only [pClosed, W, N] using hWN
    have hsplice' : pOpen =
        pClosed.take (pClosed.idxOf S + 1) ++
          pClosed.drop (pClosed.idxOf E) := by
      simpa only [pOpen, pClosed, S, E] using hsplice
    have hSOpen : S ∈ pOpen := by
      rw [hsplice', List.mem_append]
      exact Or.inl ((List.mem_take_iff_idxOf_lt hS).2 (by omega))
    have hEOpen : E ∈ pOpen := by
      rw [hsplice', List.mem_append]
      right
      rw [List.drop_eq_getElem_cons
        (List.idxOf_lt_length_iff.mpr hE),
        List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hE)]
      simp
    have hWOpen : W ∉ pOpen := by
      rw [hsplice', List.mem_append]
      push Not
      constructor
      · rw [List.mem_take_iff_idxOf_lt hW]
        omega
      · have hsplit : (pClosed.take (pClosed.idxOf E) ++
            pClosed.drop (pClosed.idxOf E)).Nodup := by
          simpa only [List.take_append_drop] using hnodup
        exact fun hdrop => hsplit.disjoint
          ((List.mem_take_iff_idxOf_lt hW).2 (by omega)) hdrop
    have hNOpen : N ∉ pOpen := by
      rw [hsplice', List.mem_append]
      push Not
      constructor
      · rw [List.mem_take_iff_idxOf_lt hN]
        omega
      · have hsplit : (pClosed.take (pClosed.idxOf E) ++
            pClosed.drop (pClosed.idxOf E)).Nodup := by
          simpa only [List.take_append_drop] using hnodup
        exact fun hdrop => hsplit.disjoint
          ((List.mem_take_iff_idxOf_lt hN).2 (by omega)) hdrop
    simpa only [fkIsingSquareWiredPathUsesLocalSide, pOpen,
      W, N, E, S] using ⟨hWOpen, hNOpen, hEOpen, hSOpen⟩
  · left
    have hES' : pClosed.idxOf E < pClosed.idxOf S := by
      simpa only [pClosed, E, S] using hES
    have hsplice' : pOpen =
        pClosed.take (pClosed.idxOf N + 1) ++
          pClosed.drop (pClosed.idxOf W) := by
      simpa only [pOpen, pClosed, N, W] using hsplice
    have hNOpen : N ∈ pOpen := by
      rw [hsplice', List.mem_append]
      exact Or.inl ((List.mem_take_iff_idxOf_lt hN).2 (by omega))
    have hWOpen : W ∈ pOpen := by
      rw [hsplice', List.mem_append]
      right
      rw [List.drop_eq_getElem_cons
        (List.idxOf_lt_length_iff.mpr hW),
        List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hW)]
      simp
    have hEOpen : E ∉ pOpen := by
      rw [hsplice', List.mem_append]
      push Not
      constructor
      · rw [List.mem_take_iff_idxOf_lt hE]
        omega
      · have hsplit : (pClosed.take (pClosed.idxOf W) ++
            pClosed.drop (pClosed.idxOf W)).Nodup := by
          simpa only [List.take_append_drop] using hnodup
        exact fun hdrop => hsplit.disjoint
          ((List.mem_take_iff_idxOf_lt hE).2 (by omega)) hdrop
    have hSOpen : S ∉ pOpen := by
      rw [hsplice', List.mem_append]
      push Not
      constructor
      · rw [List.mem_take_iff_idxOf_lt hS]
        omega
      · have hsplit : (pClosed.take (pClosed.idxOf W) ++
            pClosed.drop (pClosed.idxOf W)).Nodup := by
          simpa only [List.take_append_drop] using hnodup
        exact fun hdrop => hsplit.disjoint
          ((List.mem_take_iff_idxOf_lt hS).2 (by omega)) hdrop
    simpa only [fkIsingSquareWiredPathUsesLocalSide, pOpen,
      W, N, E, S] using ⟨hWOpen, hNOpen, hEOpen, hSOpen⟩

theorem zipWith_take_succ_take {A B C : Type*}
    (f : A → B → C) (l : List A) (r : List B) (k : Nat) :
    List.zipWith f (l.take (k + 1)) (r.take k) =
      List.zipWith f (l.take k) (r.take k) := by
  calc
    List.zipWith f (l.take (k + 1)) (r.take k) =
        (List.zipWith f (l.take (k + 1)) (r.take k)).take k := by
      symm
      rw [List.take_eq_self_iff]
      simp
    _ = List.zipWith f ((l.take (k + 1)).take k)
        ((r.take k).take k) := List.take_zipWith
    _ = List.zipWith f (l.take k) (r.take k) := by
      simp [List.take_take]

end
end StatMech.Universality
