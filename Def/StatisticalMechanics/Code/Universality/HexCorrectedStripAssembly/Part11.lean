/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripGeometry.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripAssembly.Part9


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

noncomputable def hexCSBoundaryPair
    (T L : ℕ) (hT : 0 < T) (hlocal : HexCSLocalRelation T L hT)
    (hlaw : HexCSCanonicalWindingLaw T L hT)
    (i : HexCSPairIndex T L) :
    HexMirrorBoundaryPair (hexCSDomain T L hT hlocal)
      (@hexCSHeading T L) :=
  endpointMirrorBoundaryPair_of_reflection
    (@hexCSHeading T L)
    (fun _ => rfl)
    i.1 (hexCSReflectIncidence i.1)
    (hexCSPairIndex_ne_reflect i)
    (hexCSCanonicalHeading i.1)
    (hexCSCanonicalHeading (hexCSReflectIncidence i.1))
    rfl rfl
    (hexCSReflectIncidence_mid i.1)
    (hexCSFiniteRegion_reflect hT)
    (hexCSCanonicalWinding i.1)
    (fun ts hadm => hexCS_deterministic_winding_of_law hlaw i.1 i.2.1
      (hexCSPairIndex_ne_start (hT := hT) i) ts hadm)
    (by
      rw [hexCSCanonicalHeading_reflect i.1 i.2.1
        (hexCSPairIndex_ne_start (hT := hT) i)]
      exact hexPhase_sideTilt_reflect_one _)

end
end StatMech.Universality
