/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.EdgeConfigZ.Part15
import Theorem.StatisticalMechanics.Code.Walls.fc_weightle
import Theorem.StatisticalMechanics.Code.Walls.fc_allclosed
import Theorem.StatisticalMechanics.Code.Walls.fc_bulkfraction
import Def.StatisticalMechanics.Code.Walls.fc_core.Part7
open scoped BigOperators
open SimpleGraph Filter Topology Set

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000


namespace StatMech

namespace Walls

open StatMech.FK StatMech.Lattice


variable {d : ℕ}


theorem fc_perEdgeDensityConverges_unconditional (hd : 1 ≤ d) {q : ℝ} (hq : 1 ≤ q) (s : ℝ) :
    fc_PerEdgeDensityConverges d q s :=
  fc_perEdgeDensityConverges hd hq s (fun n hn => ecz_box_edge_pos d hd hn)


theorem fc_perEdgeDensityConverges_two (s : ℝ) :
    fc_PerEdgeDensityConverges d 2 s ↔ ecz_PerEdgeDensityConverges d s := Iff.rfl


example : True := by
  have h := fc_perEdgeDensityConverges_unconditional (d := 2) (by norm_num) (q := 3) (by norm_num) 0
  obtain ⟨ρ, _⟩ := h
  trivial


theorem fc_core_report : True := trivial

end Walls
end StatMech
