/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalOffCentre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriangularOffCentre.Part5
import Theorem.StatisticalMechanics.Code.FK.HexagonalSharpness.Part5
import Theorem.StatisticalMechanics.Code.FK.HexagonalOffCentre.Part2
open scoped BigOperators Classical
open Finset Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS.RevealmentConstruction

open StatMech.OSSS.FiniteGraphBoundaryDifferential

noncomputable section

def hexagonalTransEquiv (R : Nat) (x : HexVertex) :
    HexagonalBoxVertex R ≃ HexagonalTransBoxVertex R x.1 where
  toFun y := if x.2 then
      ⟨(x.1 - y.1.1, !y.1.2), by
        refine ⟨?_, Set.mem_univ _⟩
        simpa [StatMech.FK.fvs_transBox] using y.2.1⟩
    else
      ⟨(y.1.1 + x.1, y.1.2), by
        refine ⟨?_, Set.mem_univ _⟩
        simpa [StatMech.FK.fvs_transBox] using y.2.1⟩
  invFun y := if x.2 then
      ⟨(x.1 - y.1.1, !y.1.2), by
        refine ⟨?_, Set.mem_univ _⟩
        intro i
        have hi := y.2.1 i
        change (x.1 i - y.1.1 i).natAbs ≤ R
        rw [show x.1 i - y.1.1 i = -(y.1.1 i - x.1 i) by ring,
          Int.natAbs_neg]
        exact hi⟩
    else
      ⟨(y.1.1 - x.1, y.1.2), by
        refine ⟨?_, Set.mem_univ _⟩
        simpa [StatMech.FK.fvs_transBox] using y.2.1⟩
  left_inv y := by
    cases hx : x.2
    · simp only [hx, Bool.false_eq_true, ↓reduceIte]
      apply Subtype.ext
      apply Prod.ext
      · ext i
        simp
      · rfl
    · simp only [hx, ↓reduceIte]
      apply Subtype.ext
      apply Prod.ext
      · ext i
        simp
      · simp
  right_inv y := by
    cases hx : x.2
    · simp only [hx, Bool.false_eq_true, ↓reduceIte]
      apply Subtype.ext
      apply Prod.ext
      · ext i
        simp
      · rfl
    · simp only [hx, ↓reduceIte]
      apply Subtype.ext
      apply Prod.ext
      · ext i
        simp
      · simp


end
end StatMech.FK.PeriodicPlanar
