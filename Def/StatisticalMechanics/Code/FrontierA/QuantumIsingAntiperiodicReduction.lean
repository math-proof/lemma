module
public import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingAntiperiodicProduct.Part2
public import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingSymbolReduction.Part2
public import Mathlib.Analysis.SpecialFunctions.Arcosh
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingAntiperiodicReduction.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

noncomputable def quantumIsingSpectralRoot (a : Real) : Real :=
  a + Real.sqrt (a ^ 2 - 1)

end StatMech.FrontierA
