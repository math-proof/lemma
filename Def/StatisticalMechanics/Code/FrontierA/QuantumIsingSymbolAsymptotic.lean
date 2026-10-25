/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSymbolAsymptotic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingSymbolReduction.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingBogoliubovLimit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingSymbolAsymptotic
open Filter
open scoped Topology


namespace StatMech.FrontierA

noncomputable def quantumIsingReducedParameterAtScale
    (h k t : Real) : Real :=
  Real.cosh t * ((1 + (h * t) ^ 2) / (1 - (h * t) ^ 2)) +
    Real.sinh t * (2 * (h * t) / (1 - (h * t) ^ 2)) * Real.cos k

end StatMech.FrontierA
