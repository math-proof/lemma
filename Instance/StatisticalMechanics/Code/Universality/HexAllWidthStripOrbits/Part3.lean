/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripOrbits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part18
import Theorem.StatisticalMechanics.Code.Universality.HexMirrorOrbitBoundary.Part3
import Abbrev.StatisticalMechanics.Code.Universality.HexAllWidthStripOrbits


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

noncomputable instance hexAWPairIndex_fintype (T L : ℕ) :
    Fintype (HexAWPairIndex T L) := Fintype.ofFinite _

noncomputable instance hexAWFixedIndex_fintype (T L : ℕ) (hT : 0 < T) :
    Fintype (HexAWFixedIndex T L hT) := Fintype.ofFinite _

instance hexAWPairIndex_decidableEq (T L : ℕ) :
    DecidableEq (HexAWPairIndex T L) := inferInstance

instance hexAWFixedIndex_decidableEq (T L : ℕ) (hT : 0 < T) :
    DecidableEq (HexAWFixedIndex T L hT) := inferInstance


end
end StatMech.Universality
