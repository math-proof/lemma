/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingThermodynamicLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingBoundaryComparison.Part6
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingAlmostAdditive.Part2
import Abbrev.StatisticalMechanics.Code.FrontierA.QuantumIsingThermodynamicLimit.Part2
open scoped BigOperators
open Filter


namespace StatMech.FrontierA

noncomputable def quantumIsingTwoBlockVerticalLayerWeight
    (beta h : Real) (n A B : Nat)
    (omega : QuantumIsingSpaceTimeTwoBlockConfig n A B) (t : Fin n) : Real :=
  (∏ i : Fin A, quantumIsingVerticalBondWeight beta h n
      ((omega t).1 i) ((omega (quantumIsingCyclicSucc t)).1 i)) *
    ∏ j : Fin B, quantumIsingVerticalBondWeight beta h n
      ((omega t).2 j) ((omega (quantumIsingCyclicSucc t)).2 j)

noncomputable def quantumIsingTwoBlockLongCylinderWeight
    (beta h : Real) (n A B : Nat)
    (omega : QuantumIsingSpaceTimeTwoBlockConfig n (A + 1) (B + 1)) : Real :=
  ∏ t : Fin n,
    Real.exp (beta / (4 * n) *
      quantumIsingTwoBlockLongInteraction A B (omega t)) *
      quantumIsingTwoBlockVerticalLayerWeight beta h n (A + 1) (B + 1) omega t

noncomputable def quantumIsingTwoBlockPeriodicCylinderWeight
    (beta h : Real) (n A B : Nat)
    (omega : QuantumIsingSpaceTimeTwoBlockConfig n (A + 1) (B + 1)) : Real :=
  ∏ t : Fin n,
    Real.exp (beta / (4 * n) *
      quantumIsingTwoBlockPeriodicInteraction A B (omega t)) *
      quantumIsingTwoBlockVerticalLayerWeight beta h n (A + 1) (B + 1) omega t

end StatMech.FrontierA
