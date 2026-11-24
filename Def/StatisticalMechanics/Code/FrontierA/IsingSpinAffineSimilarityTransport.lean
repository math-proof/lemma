module
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingSpinMovingMesh.Part4
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingSpinAffineSimilarityTransport
open Filter Topology
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSpinAffineSimilarityTransport.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech StatMech.FK StatMech.Ising


noncomputable def inverseUniformScaleAffineConformalMap
    (ρ : Real) (b : Complex) : Complex → Complex :=
  fun z ↦ (ρ⁻¹ : Complex) * z + b

end StatMech.FrontierA
