/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingFiniteHamiltonian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterCylinder.Part2
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
open scoped BigOperators
open Matrix


namespace StatMech.FrontierA

def quantumIsingDisagreementSet {L : Nat}
    (sigma tau : QuantumIsingChainConfig L) : Finset (Fin L) :=
  Finset.univ.filter fun i => sigma i ≠ tau i


def quantumIsingDisagreementCount {L : Nat}
    (sigma tau : QuantumIsingChainConfig L) : Nat :=
  (quantumIsingDisagreementSet sigma tau).card

end StatMech.FrontierA
