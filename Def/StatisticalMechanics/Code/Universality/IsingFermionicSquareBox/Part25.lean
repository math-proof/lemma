/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicMedialComplex.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFiniteDuality
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Mathlib.Combinatorics.SimpleGraph.Matching
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part26


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareLoopGraph (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    SimpleGraph (FKIsingSquareMedialCarrier n) where
  Adj x y :=
    (∃ d, x = .dart d ∧
      y = .dart (FKIsingMedialDart.localMate omega d)) ∨
      y = fkIsingSquareCutBondMate n hn x
  symm := by
    constructor
    intro x y h
    rcases h with ⟨d, rfl, rfl⟩ | rfl
    · left
      refine ⟨FKIsingMedialDart.localMate omega d, rfl, ?_⟩
      rw [FKIsingMedialDart.localMate_involutive]
    · right
      exact (fkIsingSquareCutBondMate_involutive n hn x).symm
  loopless := ⟨by
    intro x h
    rcases h with ⟨d, hx, hy⟩ | h
    · subst x
      injection hy with heq
      exact FKIsingMedialDart.localMate_ne omega d heq.symm
    · exact fkIsingSquareCutBondMate_ne n hn x h.symm⟩

end
end StatMech.Universality
