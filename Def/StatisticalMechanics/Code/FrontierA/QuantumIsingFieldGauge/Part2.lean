/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingFieldGauge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingFiniteHamiltonian.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingFieldGauge
open Matrix
open scoped Norms.Operator


namespace StatMech.FrontierA

noncomputable def quantumIsingFieldGaugeMatrix (L : Nat) :
    Matrix (QuantumIsingChainConfig L) (QuantumIsingChainConfig L) Complex :=
  diagonal fun sigma => (quantumIsingFieldGaugeSign sigma : Complex)

end StatMech.FrontierA
