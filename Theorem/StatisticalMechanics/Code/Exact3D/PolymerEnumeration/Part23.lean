/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Instance.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part8


namespace StatMech

namespace Exact3D

open StatMech.Lattice

noncomputable section

namespace BoundedPolymerCase

theorem finiteCubicEquivalent_iff {d R maxDegree maxRange : ℕ}
    (c c' : BoundedPolymerCase d R maxDegree maxRange) :
    finiteCubicEquivalent c c' ↔ cubicEquivalent c c' := by
  constructor
  · rintro ⟨hdegree, hrange, σ, ε, hfinite⟩
    rcases (PolymerSupport.finiteTranslationEquivalent_iff
      (c.toPolymerSupport.cubicTransform (0 : Site d) σ ε)
      c'.toPolymerSupport).mp hfinite with ⟨v, htrans⟩
    refine ⟨hdegree, hrange, v, σ, ε, ?_⟩
    calc
      c'.toPolymerSupport =
          (c.toPolymerSupport.cubicTransform (0 : Site d) σ ε).translate v :=
        htrans
      _ = c.toPolymerSupport.cubicTransform v σ ε := by
        rw [PolymerSupport.cubicTransform_zero_translate]
  · rintro ⟨hdegree, hrange, v, σ, ε, hsupport⟩
    refine ⟨hdegree, hrange, σ, ε, ?_⟩
    apply (PolymerSupport.finiteTranslationEquivalent_iff
      (c.toPolymerSupport.cubicTransform (0 : Site d) σ ε)
      c'.toPolymerSupport).mpr
    refine ⟨v, ?_⟩
    rw [hsupport, PolymerSupport.cubicTransform_zero_translate]

end BoundedPolymerCase
end
end Exact3D
end StatMech
