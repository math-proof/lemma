/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingThermodynamicLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingBoundaryComparison.Part6
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingAlmostAdditive.Part2
import Abbrev.StatisticalMechanics.Code.FrontierA.QuantumIsingThermodynamicLimit
open scoped BigOperators
open Filter


namespace StatMech.FrontierA

def quantumIsingSumBlockEquiv (A B : Nat) :
    QuantumIsingChainConfig (A + B) ≃ QuantumIsingTwoBlockConfig A B where
  toFun sigma :=
    (fun i => sigma (finSumFinEquiv (Sum.inl i)),
      fun j => sigma (finSumFinEquiv (Sum.inr j)))
  invFun pair q :=
    Sum.elim pair.1 pair.2 (finSumFinEquiv.symm q)
  left_inv sigma := by
    funext q
    obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective q
    cases s <;> simp
  right_inv pair := by
    ext i <;> simp

end StatMech.FrontierA
