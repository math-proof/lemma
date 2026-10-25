/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSectorProductComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingFiniteSpectralBridge.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingPeriodicProduct.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingReducedParameterBounds
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingAntiperiodicReduction
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingArfSandwich
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Onsager

noncomputable def quantumIsingReducedSectorProduct
    (beta h : Real) (L : Nat) (a b : Fin 2) : Real :=
  ∏ i ∈ Finset.range L, ∏ j ∈ Finset.range L,
    2 * (1 - (beta * h / (2 * L)) ^ 2) *
      (quantumIsingTrotterReducedParameter beta h L
          (2 * Real.pi * (i + (a.val : Real) / 2) / L - Real.pi) -
        Real.cos (2 * Real.pi * (j + (b.val : Real) / 2) / L))

end StatMech.FrontierA
