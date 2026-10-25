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
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingUniformMode.Part3
open Filter Set
open scoped Topology BigOperators


namespace StatMech.FrontierA

open StatMech.Onsager

noncomputable def quantumIsingTrotterModeContribution
    (beta h : Real) (L : Nat) (k : Real) : Real :=
  if L = 0 then 0 else
    (L : Real) * Real.log (1 - (beta * h / (2 * L)) ^ 2) +
      quantumIsingRapidityCorrection
        ((L : Real) * Real.arcosh
          (quantumIsingTrotterReducedParameter beta h L k))

end StatMech.FrontierA
