/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingFiniteHamiltonian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterCylinder.Part2
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Def.StatisticalMechanics.Code.FrontierA.QuantumIsingFiniteHamiltonian.Part3
open scoped BigOperators
open Matrix


namespace StatMech.FrontierA

theorem quantumIsingBoltzmannGenerator_apply
    (beta h : Real) (L : Nat)
    (sigma tau : QuantumIsingChainConfig L) :
    quantumIsingBoltzmannGenerator beta h L sigma tau =
      if sigma = tau then
        (beta / 4 * quantumIsingChainInteraction L sigma : Real)
      else if quantumIsingDisagreementCount sigma tau = 1 then
        (beta * h / 2 : Real)
      else 0 := by
  by_cases heq : sigma = tau
  · subst tau
    simp [quantumIsingBoltzmannGenerator,
      quantumIsingHamiltonian, div_eq_mul_inv]
    ring
  · by_cases hflip : quantumIsingDisagreementCount sigma tau = 1
    · simp [quantumIsingBoltzmannGenerator,
        quantumIsingHamiltonian, heq, hflip, div_eq_mul_inv]
      ring
    · simp [quantumIsingBoltzmannGenerator,
        quantumIsingHamiltonian, heq, hflip]


end StatMech.FrontierA
