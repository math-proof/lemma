/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailBoundSkeleton.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part39
import Structure.StatisticalMechanics.Code.Exact3D.TailBoundSkeleton
open scoped BigOperators


namespace StatMech

namespace Exact3D

def InsideFiniteCutoff {d : ℕ} (K : TailCutoff)
    (c : LocalPolymerCoordinate d) : Prop :=
  c.support.containedInBox K.radius ∧ c.degree ≤ K.maxDegree ∧ c.range ≤ K.maxRange


def OutsideFiniteCutoff {d : ℕ} (K : TailCutoff)
    (c : LocalPolymerCoordinate d) : Prop :=
  ¬ InsideFiniteCutoff K c


end Exact3D
end StatMech
