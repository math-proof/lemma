/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIntegration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIncidence.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDiamondIntegration.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIntegration.Part4


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

@[simp] theorem fkIsingSquareFullOrientedRadialIncrement_incidence
    (n : Nat) (hn : 0 < n)
    (e : FKIsingSquareInteriorRadialIncidence n hn) :
    fkIsingSquareFullOrientedRadialIncrement n hn
        (.inl (fkIsingSquareInteriorRadialEndpoint n hn e))
        (.inr (fkIsingSquareFullFaceOfRadialIncidence n hn e)) =
      fkIsingSquareInteriorRadialIncrement n hn e := by
  rw [fkIsingSquareFullOrientedRadialIncrement]
  split
  · rw [fkIsingSquareFullIncidenceOfAdjacent_of_incidence n hn e]
  · rename_i h
    exact False.elim
      (h (fkIsingSquareFull_radiallyAdjacent_of_incidence n hn e))

@[simp] theorem fkIsingSquareFullOrientedRadialIncrement_incidence_reverse
    (n : Nat) (hn : 0 < n)
    (e : FKIsingSquareInteriorRadialIncidence n hn) :
    fkIsingSquareFullOrientedRadialIncrement n hn
        (.inr (fkIsingSquareFullFaceOfRadialIncidence n hn e))
        (.inl (fkIsingSquareInteriorRadialEndpoint n hn e)) =
      -fkIsingSquareInteriorRadialIncrement n hn e := by
  rw [fkIsingSquareFullOrientedRadialIncrement]
  split
  · rw [fkIsingSquareFullIncidenceOfAdjacent_of_incidence n hn e]
  · rename_i h
    exact False.elim
      (h (fkIsingSquareFull_radiallyAdjacent_of_incidence n hn e))

theorem fkIsingSquareFullOrientedRadialIncrement_antisymm
    (n : Nat) (hn : 0 < n)
    (a b : FKIsingSquareFullRadialNode n) :
    fkIsingSquareFullOrientedRadialIncrement n hn a b =
      -fkIsingSquareFullOrientedRadialIncrement n hn b a := by
  classical
  cases a with
  | inl x =>
      cases b with
      | inl y => simp [fkIsingSquareFullOrientedRadialIncrement]
      | inr c =>
          by_cases h : FKIsingSquareFullRadiallyAdjacent n x c <;>
            simp [fkIsingSquareFullOrientedRadialIncrement, h]
  | inr c =>
      cases b with
      | inl x =>
          by_cases h : FKIsingSquareFullRadiallyAdjacent n x c <;>
            simp [fkIsingSquareFullOrientedRadialIncrement, h]
      | inr d => simp [fkIsingSquareFullOrientedRadialIncrement]

end
end StatMech.Universality
