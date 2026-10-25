/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Theorem.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part22


namespace StatMech

namespace Exact3D

open StatMech.Lattice

noncomputable section

namespace BoundedPolymerCase

def finiteCubicEquivalent {d R maxDegree maxRange : ℕ}
    (c c' : BoundedPolymerCase d R maxDegree maxRange) : Prop :=
  c.degree = c'.degree ∧ c.range = c'.range ∧
    ∃ (σ : Equiv.Perm (Fin d)) (ε : PolymerSupport.CoordinateReflection d),
      PolymerSupport.finiteTranslationEquivalent
        (c.toPolymerSupport.cubicTransform (0 : Site d) σ ε)
        c'.toPolymerSupport

end BoundedPolymerCase
end
end Exact3D
end StatMech
