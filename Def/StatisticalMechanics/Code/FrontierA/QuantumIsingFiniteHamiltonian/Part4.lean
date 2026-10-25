/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingFiniteHamiltonian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterCylinder.Part2
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingFiniteHamiltonian.Part3
open scoped BigOperators
open Matrix


namespace StatMech.FrontierA

noncomputable def quantumIsingQuantumPartition
    (beta h : Real) (L : Nat) : Complex :=
  (NormedSpace.exp (quantumIsingBoltzmannGenerator beta h L)).trace


noncomputable def quantumIsingTrotterStep
    (beta h : Real) (L : Nat) (t : Real) :
    Matrix (QuantumIsingChainConfig L) (QuantumIsingChainConfig L) Complex :=
  fun sigma tau =>
    (Real.exp (t * (beta / 4 * quantumIsingChainInteraction L sigma)) : Complex) *
      ((t * (beta * h / 2) : Real) : Complex) ^
        quantumIsingDisagreementCount sigma tau

end StatMech.FrontierA
