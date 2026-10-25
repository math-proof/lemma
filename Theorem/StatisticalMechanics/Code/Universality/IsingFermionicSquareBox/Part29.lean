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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part26


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

@[simp] theorem fkIsingSquareLocalSmoothingGraph_adj_dart_iff
    (n : Nat) (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (z : FKIsingSquareMedialCarrier n) :
    (fkIsingSquareLocalSmoothingGraph n omega).Adj (.dart d) z ↔
      z = .dart (FKIsingMedialDart.localMate omega d) := by
  constructor
  · rintro ⟨f, hf, rfl⟩
    injection hf with h
    subst f
    rfl
  · rintro rfl
    exact ⟨d, rfl, rfl⟩


theorem fkIsingSquareLoopGraph_isAlternating_localSmoothing
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    (fkIsingSquareLoopGraph n hn omega).IsAlternating
      (fkIsingSquareLocalSmoothingGraph n omega) := by
  intro v w w' hne hvw hvw'
  cases v with
  | source =>
      rw [fkIsingSquareLoopGraph_adj_source_iff] at hvw hvw'
      exact False.elim (hne (hvw.trans hvw'.symm))
  | terminal =>
      rw [fkIsingSquareLoopGraph_adj_terminal_iff] at hvw hvw'
      exact False.elim (hne (hvw.trans hvw'.symm))
  | dart d =>
      rw [fkIsingSquareLoopGraph_adj_dart_iff] at hvw hvw'
      rw [fkIsingSquareLocalSmoothingGraph_adj_dart_iff,
        fkIsingSquareLocalSmoothingGraph_adj_dart_iff]
      rcases hvw with hw | hw <;> rcases hvw' with hw' | hw'
      · exact False.elim (hne (hw.trans hw'.symm))
      · subst w
        subst w'
        simp only [eq_self, true_iff]
        exact fkIsingSquareCutBondMate_ne_localMate n hn omega d
      · subst w
        subst w'
        simp [fkIsingSquareCutBondMate_ne_localMate n hn omega d]
      · exact False.elim (hne (hw.trans hw'.symm))


end
end StatMech.Universality
