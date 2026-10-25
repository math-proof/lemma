/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSpatialSeam.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingAlmostAdditive.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterCylinder.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingSpatialSeam.Part4
open scoped BigOperators


namespace StatMech.FrontierA

noncomputable def quantumIsingOpenTrotterPathWeight
    (beta h : Real) (n L : Nat)
    (omega : Fin n -> QuantumIsingChainConfig (L + 1)) : Real :=
  ∏ k : Fin n, quantumIsingOpenTrotterTransferKernel beta h n L
      (omega k) (omega (quantumIsingCyclicSucc k))


noncomputable def quantumIsingOpenTrotterPathPartition
    (beta h : Real) (n L : Nat) : Real :=
  ∑ omega : Fin n -> QuantumIsingChainConfig (L + 1),
    quantumIsingOpenTrotterPathWeight beta h n L omega

end StatMech.FrontierA
