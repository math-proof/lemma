/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingFiniteHamiltonian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterCylinder.Part2
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingFiniteHamiltonian.Part2
open scoped BigOperators
open Matrix


namespace StatMech.FrontierA

noncomputable def quantumIsingBoltzmannGenerator
    (beta h : Real) (L : Nat) :
    Matrix (QuantumIsingChainConfig L) (QuantumIsingChainConfig L) Complex :=
  (-beta : Complex) • quantumIsingHamiltonian h L

end StatMech.FrontierA
