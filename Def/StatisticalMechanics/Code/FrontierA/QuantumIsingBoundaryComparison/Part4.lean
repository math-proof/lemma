/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingBoundaryComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterCylinder.Part2
import Abbrev.StatisticalMechanics.Code.FrontierA.QuantumIsingBoundaryComparison.Part2
open scoped BigOperators


namespace StatMech.FrontierA

noncomputable def quantumIsingBlockVerticalLayerWeight
    (beta h : Real) (n k L : Nat)
    (omega : QuantumIsingSpaceTimeBlockConfig n k L) (t : Fin n) : Real :=
  ∏ b : Fin k, ∏ i : Fin L,
    quantumIsingVerticalBondWeight beta h n
      (omega t b i) (omega (quantumIsingCyclicSucc t) b i)

noncomputable def quantumIsingBlockLongCylinderWeight
    (beta h : Real) (n k L : Nat)
    (omega : QuantumIsingSpaceTimeBlockConfig n (k + 1) (L + 1)) : Real :=
  ∏ t : Fin n,
    Real.exp (beta / (4 * n) *
      quantumIsingBlockLongInteraction k L (omega t)) *
      quantumIsingBlockVerticalLayerWeight beta h n (k + 1) (L + 1) omega t

noncomputable def quantumIsingBlockPeriodicCylinderWeight
    (beta h : Real) (n k L : Nat)
    (omega : QuantumIsingSpaceTimeBlockConfig n (k + 1) (L + 1)) : Real :=
  ∏ t : Fin n,
    Real.exp (beta / (4 * n) *
      quantumIsingBlockPeriodicInteraction k L (omega t)) *
      quantumIsingBlockVerticalLayerWeight beta h n (k + 1) (L + 1) omega t

end StatMech.FrontierA
