/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareSourcePhase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareSwitching


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC
  StatMech.FrontierD

noncomputable section

theorem fkIsingSquareLiftedWinding_sub_eq_turnCount_sub
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (x y : FKIsingSquareMedialCarrier n) :
    fkIsingSquareLiftedWinding n hn omega x -
        fkIsingSquareLiftedWinding n hn omega y =
      ((fkIsingSquarePhysicalTurnCount n hn omega x -
          fkIsingSquarePhysicalTurnCount n hn omega y : Int) : Real) *
        (Real.pi / 4) := by
  simp only [fkIsingSquareLiftedWinding]
  push_cast
  ring


theorem fkIsingSquare_double_visit_open_source_side_membership
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquarePathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquarePathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    (((fkIsingSquareExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .south)) <
        (fkIsingSquareExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .east))) ∧
      fkIsingSquarePathUsesLocalSide n hn
        (setOpen e.1 omega) e .west) ∨
    (((fkIsingSquareExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .north)) <
        (fkIsingSquareExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .west))) ∧
      fkIsingSquarePathUsesLocalSide n hn
        (setOpen e.1 omega) e .east) := by
  classical
  let W : FKIsingSquareMedialCarrier n := .dart (e, .west)
  let E : FKIsingSquareMedialCarrier n := .dart (e, .east)
  let pClosed := fkIsingSquareExplorationOrder n hn (setClosed e.1 omega)
  have hW : W ∈ pClosed := by
    simpa only [W, pClosed, fkIsingSquarePathUsesLocalSide] using hwest
  have hE : E ∈ pClosed := by
    simpa only [E, pClosed, fkIsingSquarePathUsesLocalSide] using heast
  rcases fkIsingSquare_double_visit_open_splice_support
      n hn omega e hwest heast with ⟨hsplice, hSE⟩ | ⟨hsplice, hNW⟩
  · left
    refine ⟨hSE, ?_⟩
    change W ∈ fkIsingSquareExplorationOrder n hn (setOpen e.1 omega)
    rw [hsplice, List.mem_append]
    left
    have hW' : (.dart (e, .west) : FKIsingSquareMedialCarrier n) ∈
        fkIsingSquareExplorationOrder n hn (setClosed e.1 omega) := by
      simpa only [W, pClosed] using hW
    exact (List.mem_take_iff_idxOf_lt hW').2 (by omega)
  · right
    refine ⟨hNW, ?_⟩
    change E ∈ fkIsingSquareExplorationOrder n hn (setOpen e.1 omega)
    rw [hsplice, List.mem_append]
    left
    have hE' : (.dart (e, .east) : FKIsingSquareMedialCarrier n) ∈
        fkIsingSquareExplorationOrder n hn (setClosed e.1 omega) := by
      simpa only [E, pClosed] using hE
    exact (List.mem_take_iff_idxOf_lt hE').2 (by omega)


end
end StatMech.Universality
