module
public import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingUniformArcosh
public import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingSectorProductReduction
public import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingScalarNormalizationLimit
public import Theorem.StatisticalMechanics.Code.Onsager.RiemannPeriodicMidpoint
public import Mathlib.Analysis.Calculus.MeanValue
public import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingUniformMode
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

noncomputable def quantumIsingModeScalarNormalization
    (beta h : Real) (n : Nat) : Real :=
  (n + 1 : Real) * Real.log
    (1 - (beta * h / (2 * (n + 1 : Real))) ^ 2)

end StatMech.FrontierA
