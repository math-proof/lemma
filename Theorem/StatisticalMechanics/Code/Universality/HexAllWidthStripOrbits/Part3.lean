/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripOrbits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part18
import Theorem.StatisticalMechanics.Code.Universality.HexMirrorOrbitBoundary.Part3
import Def.StatisticalMechanics.Code.Universality.HexAllWidthStripOrbits.Part4


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

theorem hexAWIncidenceRank_injective {T L : ℕ} :
    Function.Injective (@hexAWIncidenceRank T L) := by
  intro e f h
  exact (Fintype.equivFin (HexAWIncidence T L)).injective (Fin.ext h)


end
end StatMech.Universality
