/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalFreeBoxLocalObservables.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalTorusLocalObservables.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.ScalarCumulantsContinuity
import Theorem.StatisticalMechanics.Code.FrontierB.FreeBoxEvenLimit.Part6
open Filter Finset MeasureTheory Topology
open scoped BigOperators


namespace StatMech.FrontierA

open ProbabilityTheory StatMech Ising Lattice Sharpness StatMech.FrontierB
  StatMech.Probability

noncomputable section

variable {d : Nat}

theorem freeBox_walshChar_infiniteRestriction
    (A : Finset (Site d)) (B : Finset {x // x ∈ A})
    (omega : ConfigSpace (Site d)) :
    khc_walshChar B (criticalInfiniteLocalRestriction A omega) =
      (-1 : Real) ^ B.card *
        spinProd (B.map (Function.Embedding.subtype fun x ↦ x ∈ A)) omega := by
  rw [khc_walshChar_eq_negOnePow_spinProd]
  congr 1
  unfold spinProd criticalInfiniteLocalRestriction
  rw [Finset.prod_map]
  apply Finset.prod_congr rfl
  intro x hx
  unfold spin
  rfl


end
end StatMech.FrontierA
