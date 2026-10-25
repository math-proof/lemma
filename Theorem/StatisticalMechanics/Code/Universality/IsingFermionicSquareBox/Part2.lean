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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareBoundarySite_mem_box (n : Nat)
    (i : FKIsingSquareBoundaryIndex n) :
    fkIsingSquareBoundarySite n i ∈ box 2 n := by
  rcases i with ⟨side, k⟩
  cases side <;> intro j <;> fin_cases j <;>
    simp [fkIsingSquareBoundarySite, centered_offset_natAbs_le,
      centered_reverse_natAbs_le]


end
end StatMech.Universality
