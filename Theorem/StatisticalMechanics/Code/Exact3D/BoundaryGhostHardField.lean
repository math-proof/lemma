module
public import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part121
public import Theorem.StatisticalMechanics.Code.Exact3D.FiniteHardField.Part3
public import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
public import Def.StatisticalMechanics.Code.Exact3D.BoundaryGhostHardField
open Filter
open scoped BigOperators Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Exact3D

theorem boundaryGhostOnePointObservable_eq (d n : ℕ)
    (σ : BoundaryGhostConfig d n) :
    boundaryGhostOnePointObservable d n σ =
      Ising.spin σ (some (IsingFK.boxOrigin d n)) * Ising.spin σ none := by
  simp [boundaryGhostOnePointObservable, finiteBoundaryGhostOnePointSource,
    Ising.spinProd]


end Exact3D
end StatMech
