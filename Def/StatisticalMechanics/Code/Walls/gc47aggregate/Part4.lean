/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc47aggregate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc46redistribute.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc47aggregate.Part3
open Finset BigOperators SimpleGraph
open scoped symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.multiGoal false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000


namespace StatMech.Walls

open StatMech.Sharpness.RandomCurrent (sources connK degK adjStep compOf switching_card
  exists_conn_set sources_symmDiff path_exists mem_sources)

noncomputable def gc47_defectOverflow : Finset (Σ _ : Finset (Fin 5), Finset (Fin 5)) :=
  (({({0, 1, 3, 4} : Finset (Fin 5)), {0, 2, 3, 4}, {1, 2, 3, 4}} : Finset (Finset (Fin 5)))).sigma
    (fun M => gc45_evenSub gc46_defectEnds M)


end StatMech.Walls
