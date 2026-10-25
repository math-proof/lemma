/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripGeometry.Part11
import Instance.StatisticalMechanics.Code.Universality.HexCorrectedStripAssembly.Part2


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

noncomputable def hexCSIncidenceRank {T L : ℕ}
    (e : HexCSIncidence T L) : ℕ :=
  (Fintype.equivFin (HexCSIncidence T L) e).val

end
end StatMech.Universality
