/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripOrbits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part18
import Theorem.StatisticalMechanics.Code.Universality.HexMirrorOrbitBoundary.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripOrbits.Part3


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

abbrev HexAWPairIndex (T L : ℕ) :=
  {e : HexAWIncidence T L //
    e ∈ hexAWBoundaryIncidences T L ∧
      hexAWIncidenceRank e <
        hexAWIncidenceRank (hexAWReflectIncidence e)}


abbrev HexAWFixedIndex (T L : ℕ) (hT : 0 < T) :=
  {e : HexAWIncidence T L //
    e ∈ hexAWBoundaryIncidences T L ∧
      hexAWReflectIncidence e = e ∧
      e ≠ hexAWStartIncidence T L hT}

end
end StatMech.Universality
