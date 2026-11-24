module
public import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingUniformArcosh
public import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingSectorProductReduction
public import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingScalarNormalizationLimit
public import Theorem.StatisticalMechanics.Code.Onsager.RiemannPeriodicMidpoint
public import Mathlib.Analysis.Calculus.MeanValue
public import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingUniformMode.Part4
open Filter Set
open scoped Topology BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingUniformMode.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech.Onsager

noncomputable def quantumIsingElevenSectorLogDensity
    (beta h : Real) (n : Nat) : Real := by
  letI : Fact (2 < n + 3) := ⟨by omega⟩
  exact (2 * Real.log
    ‖quantumIsingNormalizedSpinSector beta h (n + 3) 1 1‖) / (n + 3)

end StatMech.FrontierA
