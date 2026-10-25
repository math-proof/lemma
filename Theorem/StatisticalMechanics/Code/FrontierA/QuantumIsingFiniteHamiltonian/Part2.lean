/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingFiniteHamiltonian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterCylinder.Part2
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Def.StatisticalMechanics.Code.FrontierA.QuantumIsingFiniteHamiltonian.Part2
open scoped BigOperators
open Matrix


namespace StatMech.FrontierA

theorem quantumIsingHamiltonian_apply_diag
    (h : Real) (L : Nat) (sigma : QuantumIsingChainConfig L) :
    quantumIsingHamiltonian h L sigma sigma =
      -(quantumIsingChainInteraction L sigma : Complex) / 4 := by
  simp [quantumIsingHamiltonian]

theorem quantumIsingHamiltonian_apply_oneFlip
    (h : Real) (L : Nat) (sigma tau : QuantumIsingChainConfig L)
    (hne : sigma ≠ tau) (hflip : quantumIsingDisagreementCount sigma tau = 1) :
    quantumIsingHamiltonian h L sigma tau = -(h : Complex) / 2 := by
  simp [quantumIsingHamiltonian, hne, hflip]

theorem quantumIsingHamiltonian_apply_other
    (h : Real) (L : Nat) (sigma tau : QuantumIsingChainConfig L)
    (hne : sigma ≠ tau) (hflip : quantumIsingDisagreementCount sigma tau ≠ 1) :
    quantumIsingHamiltonian h L sigma tau = 0 := by
  simp [quantumIsingHamiltonian, hne, hflip]


theorem quantumIsingHamiltonian_isHermitian (h : Real) (L : Nat) :
    (quantumIsingHamiltonian h L).IsHermitian := by
  rw [Matrix.IsHermitian.ext_iff]
  intro sigma tau
  by_cases heq : sigma = tau
  · subst tau
    simp [quantumIsingHamiltonian]
  · have heq' : tau ≠ sigma := Ne.symm heq
    by_cases hflip : quantumIsingDisagreementCount sigma tau = 1
    · have hflip' : quantumIsingDisagreementCount tau sigma = 1 := by
        rw [quantumIsingDisagreementCount_comm]
        exact hflip
      simp [quantumIsingHamiltonian, heq, heq', hflip, hflip']
    · have hflip' : quantumIsingDisagreementCount tau sigma ≠ 1 := by
        rw [quantumIsingDisagreementCount_comm]
        exact hflip
      simp [quantumIsingHamiltonian, heq, heq', hflip, hflip']


end StatMech.FrontierA
