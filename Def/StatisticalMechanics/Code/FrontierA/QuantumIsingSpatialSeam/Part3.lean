/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSpatialSeam.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingAlmostAdditive.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterCylinder.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingSpatialSeam.Part2
open scoped BigOperators


namespace StatMech.FrontierA

noncomputable def quantumIsingOpenSpatialTrotterWeight
    (beta : Real) (n L : Nat)
    (sigma : QuantumIsingChainConfig (L + 1)) : Real :=
  Real.exp (beta / (4 * (n : Real)) *
    quantumIsingOpenChainInteraction L sigma)


end StatMech.FrontierA
