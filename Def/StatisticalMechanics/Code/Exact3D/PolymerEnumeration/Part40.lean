/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Theorem.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part33


namespace StatMech

namespace Exact3D

open StatMech.Lattice

noncomputable section

namespace BoundedPolymerCase

def CubicRepresentativeTableCovers {d R maxDegree maxRange : ℕ}
    (T : RatInterval.CaseTable (BoundedPolymerCase d R maxDegree maxRange)) :
    Prop :=
  ∀ c : BoundedPolymerCase d R maxDegree maxRange,
    ∃ r, r ∈ T.cases ∧ cubicEquivalent r c


noncomputable def classifyByCubicRepresentative {d R maxDegree maxRange : ℕ}
    (T : RatInterval.CaseTable (BoundedPolymerCase d R maxDegree maxRange))
    (hcover : CubicRepresentativeTableCovers T)
    (c : BoundedPolymerCase d R maxDegree maxRange) :
    BoundedPolymerCase d R maxDegree maxRange :=
  Classical.choose (hcover c)


end BoundedPolymerCase
end
end Exact3D
end StatMech
