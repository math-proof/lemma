/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicLift.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusCycleTopology.Part2
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusPeriodicLift
open scoped BigOperators


namespace StatMech.FrontierA

@[simp] theorem triangularIntReduce_zero (L : Nat) :
    triangularIntReduce L 0 = 0 := by
  apply Prod.ext <;> simp [triangularIntReduce]

@[simp] theorem triangularIntReduce_add (L : Nat) (p q : Int × Int) :
    triangularIntReduce L (p + q) =
      triangularIntReduce L p + triangularIntReduce L q := by
  apply Prod.ext <;> simp [triangularIntReduce]

theorem triangularIntReduce_sum
    {alpha : Type*} (L : Nat) (s : Finset alpha) (f : alpha -> Int × Int) :
    triangularIntReduce L (∑ i ∈ s, f i) =
      ∑ i ∈ s, triangularIntReduce L (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        triangularIntReduce_add, ih]

theorem triangularIntReduce_step
    (L : Nat) (a : Fin 6) :
    triangularIntReduce L (triangularIntStep a) =
      -triangularTorusDirectionStep L a := by
  fin_cases a <;>
    simp [triangularIntReduce, triangularIntStep,
      triangularTorusDirectionStep]

end StatMech.FrontierA
