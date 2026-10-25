/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredEndpoints.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredEuler
import Theorem.StatisticalMechanics.Code.FK.EdgeConfigZ.Part15
import Theorem.StatisticalMechanics.Code.FrontierB.BoxGraphPath.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredEndpoints.Part2
open Finset SimpleGraph


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierB
  StatMech.FrontierD

noncomputable section

noncomputable def fkIsingSquareWiredArcEquivIcc
    (n : Nat) :
    {x : (fkSquareBoxPlanar n).V // fkIsingSquareWiredArc n x} ≃
      {z : Int // z ∈ Finset.Icc (-(n : Int)) (n : Int)} where
  toFun x := ⟨x.1.1 1, by
    rw [Finset.mem_Icc]
    exact fkIsingSquareVertex_coordinate_bounds n x.1 1⟩
  invFun z := ⟨⟨![-(n : Int), z.1], by
    intro i
    fin_cases i
    · simp
    · have hz := z.2
      rw [Finset.mem_Icc] at hz
      have habs : |z.1| ≤ (n : Int) := abs_le.mpr hz
      rw [Int.abs_eq_natAbs] at habs
      exact_mod_cast habs⟩, rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    fin_cases i
    · exact x.2.symm
    · rfl
  right_inv z := by
    apply Subtype.ext
    rfl

end
end StatMech.Universality
