/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSpatialSeam.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingAlmostAdditive.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterCylinder.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingSpatialSeam.Part3
open scoped BigOperators


namespace StatMech.FrontierA

noncomputable def quantumIsingOpenTrotterTransferKernel
    (beta h : Real) (n L : Nat)
    (sigma tau : QuantumIsingChainConfig (L + 1)) : Real :=
  quantumIsingOpenSpatialTrotterWeight beta n L sigma *
    ∏ i : Fin (L + 1), quantumIsingTrotterKernel beta h n (sigma i) (tau i)

end StatMech.FrontierA
