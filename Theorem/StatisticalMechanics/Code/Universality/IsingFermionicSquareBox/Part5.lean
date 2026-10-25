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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part4


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareBoundaryOrder_length (n : Nat) :
    (fkIsingSquareBoundaryOrder n).length = 8 * n := by
  simp [fkIsingSquareBoundaryOrder]

theorem fkIsingSquareBoundaryOrder_nodup (n : Nat) :
    (fkIsingSquareBoundaryOrder n).Nodup := by
  unfold fkIsingSquareBoundaryOrder
  exact List.nodup_ofFn.mpr
    (fkIsingSquareBoundaryOrderEquiv n).symm.injective

theorem fkIsingSquareBoundarySucc_ne (n : Nat) (hn : 0 < n)
    (i : FKIsingSquareBoundaryIndex n) :
    fkIsingSquareBoundarySucc n hn i ≠ i := by
  intro h
  have h' := congrArg (fkIsingSquareBoundaryOrderEquiv n) h
  have hsucc : finitePeriodicSucc (by omega : 0 < 8 * n)
      (fkIsingSquareBoundaryOrderEquiv n i) =
        fkIsingSquareBoundaryOrderEquiv n i := by
    simpa [fkIsingSquareBoundarySucc] using h'
  exact finitePeriodicSucc_ne_self (by omega : 1 < 8 * n) _ hsucc


end
end StatMech.Universality
