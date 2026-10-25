/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingFiniteHamiltonian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterCylinder.Part2
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Def.StatisticalMechanics.Code.FrontierA.QuantumIsingFiniteHamiltonian
open scoped BigOperators
open Matrix


namespace StatMech.FrontierA

theorem quantumIsingDisagreementSet_comm {L : Nat}
    (sigma tau : QuantumIsingChainConfig L) :
    quantumIsingDisagreementSet sigma tau =
      quantumIsingDisagreementSet tau sigma := by
  classical
  ext i
  simp [quantumIsingDisagreementSet, ne_comm]

theorem quantumIsingDisagreementCount_comm {L : Nat}
    (sigma tau : QuantumIsingChainConfig L) :
    quantumIsingDisagreementCount sigma tau =
      quantumIsingDisagreementCount tau sigma := by
  rw [quantumIsingDisagreementCount, quantumIsingDisagreementCount,
    quantumIsingDisagreementSet_comm]

@[simp] theorem quantumIsingDisagreementCount_self {L : Nat}
    (sigma : QuantumIsingChainConfig L) :
    quantumIsingDisagreementCount sigma sigma = 0 := by
  simp [quantumIsingDisagreementCount, quantumIsingDisagreementSet]

theorem quantumIsingDisagreementCount_eq_zero_iff {L : Nat}
    (sigma tau : QuantumIsingChainConfig L) :
    quantumIsingDisagreementCount sigma tau = 0 ↔ sigma = tau := by
  classical
  unfold quantumIsingDisagreementCount quantumIsingDisagreementSet
  rw [Finset.card_eq_zero,
    Finset.filter_eq_empty_iff]
  constructor
  · intro h
    funext i
    by_contra hne
    exact h (Finset.mem_univ i) hne
  · intro h i hi
    subst tau
    simp


end StatMech.FrontierA
