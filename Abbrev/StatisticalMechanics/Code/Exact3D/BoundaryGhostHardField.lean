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
open Filter
open scoped BigOperators Topology


namespace StatMech

namespace Exact3D

abbrev BoundaryGhostConfig (d n : ℕ) :=
  ConfigSpace (Option (FK.boxVerts d n))


end Exact3D
end StatMech
