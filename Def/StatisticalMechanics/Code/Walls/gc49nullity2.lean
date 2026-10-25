/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc49nullity2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc48pairinject.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc49nullity2
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

section Abstract

open Classical

variable {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]


def gc49_InnerDom (ends : ι → Sym2 W) (o x y g : W) : Prop :=
    (∑ n₁ ∈ (univ : Finset ι).powerset.filter (fun S => sources ends S = (∅ : Finset W)),
        #((univ \ n₁).powerset.filter
          (fun n₂ => sources ends n₂ = ({o, x} : Finset W) ∧ connK ends (n₁ ∪ n₂) x g)))
      ≤ ∑ n₁ ∈ (univ : Finset ι).powerset.filter (fun S => sources ends S = (∅ : Finset W)),
          #((univ \ n₁).powerset.filter
            (fun m₂ => sources ends m₂ = ({o, x, y, g} : Finset W)
              ∧ connK ends (n₁ ∪ m₂) o x ∧ connK ends (n₁ ∪ m₂) o y ∧ connK ends (n₁ ∪ m₂) o g))


end Abstract
end StatMech.Walls
