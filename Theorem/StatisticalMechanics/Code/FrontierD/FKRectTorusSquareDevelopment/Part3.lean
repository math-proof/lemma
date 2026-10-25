/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDevelopedWinding.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetFull.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareDevelopment.Part3


namespace StatMech.FrontierD

noncomputable section

theorem fkRectSquareDevelopPoint_even_vertical (X k : Int) :
    fkRectSquareDevelopPoint (X, 2 * k - 1) -
        fkRectSquareDevelopPoint (X, 2 * k) = (0, 1) := by
  apply Prod.ext <;> simp [fkRectSquareDevelopPoint] <;> omega


theorem fkRectSquareDevelopPoint_even_diagonal (X k : Int) :
    fkRectSquareDevelopPoint (X - 1, 2 * k - 1) -
        fkRectSquareDevelopPoint (X, 2 * k) = (-1, 0) := by
  apply Prod.ext <;> simp [fkRectSquareDevelopPoint] <;> omega


theorem fkRectSquareDevelopPoint_odd_vertical (X k : Int) :
    fkRectSquareDevelopPoint (X, 2 * k) -
        fkRectSquareDevelopPoint (X, 2 * k + 1) = (-1, 0) := by
  apply Prod.ext <;> simp [fkRectSquareDevelopPoint] <;> omega


theorem fkRectSquareDevelopPoint_odd_diagonal (X k : Int) :
    fkRectSquareDevelopPoint (X, 2 * k) -
        fkRectSquareDevelopPoint (X - 1, 2 * k + 1) = (0, 1) := by
  apply Prod.ext <;> simp [fkRectSquareDevelopPoint] <;> omega


theorem fkRectLiftedIndexedEdgeEnds_squareStep
    (R : FKRectTorus) (e : R.EdgeIndex) :
    fkRectSquareDevelopPoint (fkRectLiftedIndexedEdgeEnds R e).2 -
        fkRectSquareDevelopPoint (fkRectLiftedIndexedEdgeEnds R e).1 =
      (-1, 0) ∨
    fkRectSquareDevelopPoint (fkRectLiftedIndexedEdgeEnds R e).2 -
        fkRectSquareDevelopPoint (fkRectLiftedIndexedEdgeEnds R e).1 =
      (0, 1) := by
  rcases e with ⟨b, x, y⟩
  cases b <;> by_cases hy : Even y.val
  · left
    have hyeven := hy
    obtain ⟨k, hk⟩ := hy
    have hk' : (y.val : Int) = (k : Int) + k := by
      exact_mod_cast hk
    simp only [fkRectLiftedIndexedEdgeEnds, Bool.false_eq_true,
      ↓reduceIte, hyeven]
    rw [show (y.val : Int) = 2 * (k : Int) by omega]
    exact fkRectSquareDevelopPoint_even_diagonal x.val k
  · right
    have hodd : Odd y.val := Nat.not_even_iff_odd.mp hy
    obtain ⟨k, hk⟩ := hodd
    have hk' : (y.val : Int) = 2 * (k : Int) + 1 := by
      exact_mod_cast hk
    simp only [fkRectLiftedIndexedEdgeEnds, Bool.false_eq_true,
      ↓reduceIte, hy]
    rw [hk']
    simpa using fkRectSquareDevelopPoint_odd_diagonal x.val k
  · right
    obtain ⟨k, hk⟩ := hy
    have hk' : (y.val : Int) = (k : Int) + k := by
      exact_mod_cast hk
    simp only [fkRectLiftedIndexedEdgeEnds, ↓reduceIte]
    rw [show (y.val : Int) = 2 * (k : Int) by omega]
    exact fkRectSquareDevelopPoint_even_vertical x.val k
  · left
    have hodd : Odd y.val := Nat.not_even_iff_odd.mp hy
    obtain ⟨k, hk⟩ := hodd
    have hk' : (y.val : Int) = 2 * (k : Int) + 1 := by
      exact_mod_cast hk
    simp only [fkRectLiftedIndexedEdgeEnds, ↓reduceIte]
    rw [hk']
    simpa using fkRectSquareDevelopPoint_odd_vertical x.val k


end
end StatMech.FrontierD
