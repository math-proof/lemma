/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc40count.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Walls.gc39threereplica.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc40count.Part3
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech.Sharpness.RandomCurrent (sources connK degK adjStep compOf switching_card
  exists_conn_set sources_symmDiff path_exists mem_sources)


section Abstract

variable {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]


def gc40_EWeightedCountResidue (ends : ι → Sym2 W) (o x y g : W) : Prop :=
  (∑ S₁ ∈ (univ : Finset ι).powerset.filter (fun S => sources ends S = ({o, g} : Finset W)),
      (if connK ends (univ \ S₁) y g then gc40_E ends (univ \ S₁) else 0))
    ≤ ∑ S₁ ∈ (univ : Finset ι).powerset.filter
        (fun S => sources ends S = ({o, x, y, g} : Finset W)), gc40_L ends S₁ o x y g


end Abstract
end StatMech.Walls
