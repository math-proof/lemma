/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part121
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteHardField.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Abbrev.StatisticalMechanics.Code.Exact3D.BoundaryGhostHardField
open Filter
open scoped BigOperators Topology


namespace StatMech

namespace Exact3D

noncomputable def boundaryGhostOriginalBase (d n : ℕ) (β : ℝ)
    (σ : BoundaryGhostConfig d n) : ℝ :=
  Sharpness.boltzmannJ (FK.boxGraph d n) β (fun _ => 1)
    (fun x => σ (some x))


noncomputable def boundaryGhostOnePointObservable (d n : ℕ)
    (σ : BoundaryGhostConfig d n) : ℝ :=
  Ising.spinProd (finiteBoundaryGhostOnePointSource d n) σ


end Exact3D
end StatMech
