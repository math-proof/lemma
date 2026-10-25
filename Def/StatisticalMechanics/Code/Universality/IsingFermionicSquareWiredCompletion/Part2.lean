/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part39
import Mathlib.Logic.Equiv.Fintype
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareLeftVerticalLower (n : Nat) (_hn : 0 < n)
    (k : Fin (2 * n)) : (fkSquareBoxPlanar n).V :=
  ⟨![-(n : Int), -(n : Int) + (k.val : Int)], by
    intro i
    fin_cases i
    · simp
    · simp
      have hk := k.isLt
      omega⟩

end
end StatMech.Universality
