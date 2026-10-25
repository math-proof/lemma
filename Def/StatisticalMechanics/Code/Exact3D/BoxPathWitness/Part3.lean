/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoxPathWitness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part121
import Theorem.StatisticalMechanics.Code.Percolation.GridBoxConnected.Part2
import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part3
open Filter


namespace StatMech

namespace Exact3D

open StatMech.Lattice


def boxGraphSomeHom (d n : ℕ) :
    (FK.boxGraph d n) →g Sharpness.withGhost (FK.boxGraph d n) where
  toFun := some
  map_rel' := by
    intro a b hab
    simpa using hab


end Exact3D
end StatMech
