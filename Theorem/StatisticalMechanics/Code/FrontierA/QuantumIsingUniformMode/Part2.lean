/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingUniformMode.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingUniformArcosh
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingSectorProductReduction
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingScalarNormalizationLimit
import Theorem.StatisticalMechanics.Code.Onsager.RiemannPeriodicMidpoint
import Mathlib.Analysis.Calculus.MeanValue
import Def.StatisticalMechanics.Code.FrontierA.QuantumIsingUniformMode.Part2
open Filter Set
open scoped Topology BigOperators


namespace StatMech.FrontierA

open StatMech.Onsager

theorem quantumIsingModeScalarNormalization_tendsto_zero
    (beta h : Real) (hbeta : 0 < beta) (hh : 0 < h) :
    Tendsto (quantumIsingModeScalarNormalization beta h) atTop (nhds 0) := by
  simpa only [quantumIsingModeScalarNormalization] using
    quantumIsingTrotterScalarNormalization_tendsto_zero beta h hbeta hh

end StatMech.FrontierA
