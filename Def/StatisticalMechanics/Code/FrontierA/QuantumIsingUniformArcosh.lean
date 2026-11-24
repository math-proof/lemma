module
public import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingUniformAsymptotic
public import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingArcoshAsymptotic
public import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingReducedParameterBounds
open Filter Set
open scoped Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingUniformArcosh.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

noncomputable def quantumIsingScaledArcosh
    (beta h : Real) (n : Nat) (k : Real) : Real :=
  (n + 1 : Real) * Real.arcosh
    (quantumIsingTrotterReducedParameter beta h (n + 1) k)

end StatMech.FrontierA
