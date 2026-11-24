module
public import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
public import Theorem.StatisticalMechanics.Code.FK.EdgeConfigZ.Part15
public import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeRelabel
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingSpinConformalScaling.Part2
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingSpinMovingMesh.Part3
open Filter Topology
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSpinMovingMesh.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech StatMech.FK StatMech.Ising


noncomputable def inverseUniformScaleConformalMap
    (rho : Real) : Complex → Complex :=
  fun z ↦ (rho⁻¹ : Complex) * z

end StatMech.FrontierA
