/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingFiniteHamiltonian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterCylinder.Part2
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingFiniteHamiltonian
open scoped BigOperators
open Matrix


namespace StatMech.FrontierA

noncomputable def quantumIsingHamiltonian
    (h : Real) (L : Nat) :
    Matrix (QuantumIsingChainConfig L) (QuantumIsingChainConfig L) Complex :=
  fun sigma tau =>
    if sigma = tau then
      -(quantumIsingChainInteraction L sigma : Complex) / 4
    else if quantumIsingDisagreementCount sigma tau = 1 then
      -(h : Complex) / 2
    else 0

end StatMech.FrontierA
