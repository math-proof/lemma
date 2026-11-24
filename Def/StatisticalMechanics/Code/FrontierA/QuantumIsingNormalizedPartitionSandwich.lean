module
public import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingFiniteSpectralBridge.Part2
public import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingSectorBounds
public import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingArfSandwich
public import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingThermodynamicLimit.Part7


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingNormalizedPartitionSandwich.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech.Onsager

noncomputable def quantumIsingNormalizedDiagonalPartition
    (beta h : Real) (L : Nat) : Real :=
  Real.exp (-quantumIsingVerticalCoupling beta h L) ^ (L * L) *
    quantumIsingClassicalCylinderPartition beta h L L

end StatMech.FrontierA
