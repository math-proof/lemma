/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc51minpath.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc50threereplica.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc51minpath
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
  switching_card₂ connK_symm exists_conn_set sources_symmDiff path_exists mem_sources)

section Abstract

open Classical

variable {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]


noncomputable def gc51_LblockSet (ends : ι → Sym2 W) (K : Finset ι) (o x g : W) : Finset (Finset ι) :=
  (univ \ K).powerset.filter (fun L => sources ends L = (∅ : Finset W) ∧ connK ends (K ∪ L) x g)


noncomputable def gc51_RblockSet (ends : ι → Sym2 W) (K : Finset ι) (o x y g : W) :
    Finset (Finset ι) :=
  (univ \ K).powerset.filter (fun Q => sources ends Q = ({y, g} : Finset W)
      ∧ connK ends (K ∪ Q) o x ∧ connK ends (K ∪ Q) o y ∧ connK ends (K ∪ Q) o g)


end Abstract
end StatMech.Walls
