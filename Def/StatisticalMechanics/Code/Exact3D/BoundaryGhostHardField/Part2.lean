module
public import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part121
public import Theorem.StatisticalMechanics.Code.Exact3D.FiniteHardField.Part3
public import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
public import Theorem.StatisticalMechanics.Code.Exact3D.BoundaryGhostHardField
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

noncomputable def boundaryGhostMismatchCount (d n : ℕ)
    (σ : BoundaryGhostConfig d n) : ℕ :=
  ((Finset.univ : Finset (FK.boxVerts d n)).filter
    (fun x => FK.boxBoundary d n x ∧ σ (some x) ≠ σ none)).card


end Exact3D
end StatMech
