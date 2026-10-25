/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc40count.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Walls.gc39threereplica.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc40count.Part2
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


noncomputable def gc40_L (ends : ι → Sym2 W) (S₁ : Finset ι) (o x y g : W) : ℕ :=
  #((univ \ S₁).powerset.filter (fun S₂ => sources ends S₂ = (∅ : Finset W)
      ∧ connK ends (S₁ ∪ S₂) o x ∧ connK ends (S₁ ∪ S₂) o y ∧ connK ends (S₁ ∪ S₂) o g))


end Abstract
end StatMech.Walls
