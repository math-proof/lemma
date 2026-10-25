/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSpinMovingMesh.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.FK.EdgeConfigZ.Part15
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeRelabel
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSpinConformalScaling.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSpinMovingMesh.Part2
open Filter Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech StatMech.FK StatMech.Ising


noncomputable def squareBoxRenormalizedSpinCorrelation
    (ι : Type*) [Fintype ι]
    (δ : Nat → Real) (β h : Real) (radius : Nat → Nat)
    (marked : ∀ n, ι ↪ boxVerts 2 (radius n)) : Nat → Real :=
  spinRenormalizedCorrelation ι δ
    (squareBoxMovingSpinCorrelation ι β h radius marked)


end StatMech.FrontierA
