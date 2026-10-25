/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingThermodynamicLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingBoundaryComparison.Part6
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingAlmostAdditive.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingThermodynamicLimit.Part6
open scoped BigOperators
open Filter


namespace StatMech.FrontierA

noncomputable def quantumIsingClassicalLogPressureLimit
    (beta h : Real) (n : Nat) (hbeta : 0 ≤ beta) : Real :=
  (quantumIsingClassicalLogPartitionSequence_almostAdditive beta h n hbeta).limit


end StatMech.FrontierA
