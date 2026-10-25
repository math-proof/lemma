/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripOrbits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part18
import Theorem.StatisticalMechanics.Code.Universality.HexMirrorOrbitBoundary.Part3
import Def.StatisticalMechanics.Code.Universality.HexAllWidthStripOrbits.Part3


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

noncomputable instance hexAWIncidence_fintype (T L : ℕ) :
    Fintype (HexAWIncidence T L) :=
  Fintype.ofEquiv (HexAWVertex T L × Fin 3) (hexAWIncidenceEquiv T L)


end
end StatMech.Universality
