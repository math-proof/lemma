/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Def.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part31


namespace StatMech

namespace Exact3D

open StatMech.Lattice

noncomputable section

namespace BoundedPolymerCase

@[simp] theorem cubicRepresentative_class {d R maxDegree maxRange : ℕ}
    (q : CubicClass d R maxDegree maxRange) :
    cubicClass (cubicRepresentative q) = q := by
  simp [cubicClass, cubicRepresentative, Quotient.out_eq q]


theorem cubicRepresentative_equivalent {d R maxDegree maxRange : ℕ}
    (c : BoundedPolymerCase d R maxDegree maxRange) :
    cubicEquivalent (cubicRepresentative (cubicClass c)) c := by
  have hq :
      cubicClass (cubicRepresentative (cubicClass c)) = cubicClass c :=
    cubicRepresentative_class (cubicClass c)
  exact Quotient.exact hq


end BoundedPolymerCase
end
end Exact3D
end StatMech
