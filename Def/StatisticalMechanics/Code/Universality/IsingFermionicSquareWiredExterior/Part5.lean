/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredExterior.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquarePrimalConnectivity.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredExterior.Part3
open SimpleGraph


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareWiredPred (n : Nat)
    (x : (fkSquareBoxPlanar n).V)
    (hx : fkIsingSquareWiredArc n x)
    (hgt : -(n : Int) < x.1 1) : (fkSquareBoxPlanar n).V :=
  ⟨![-(n : Int), x.1 1 - 1], by
    intro i
    fin_cases i
    · simp
    · have hb := fkIsingSquareVertex_coordinate_bounds n x 1
      have habs : |x.1 1 - 1| ≤ (n : Int) := by
        rw [abs_le]
        omega
      rw [Int.abs_eq_natAbs] at habs
      exact_mod_cast habs⟩

end
end StatMech.Universality
