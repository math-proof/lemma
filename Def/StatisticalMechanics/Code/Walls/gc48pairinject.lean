/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc48pairinject.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc47aggregate.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc48pairinject
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


noncomputable def gc48_LHSdoubled (ends : ι → Sym2 W) (o x y g : W) :
    Finset (Finset ι × Finset ι) :=
  (univ : Finset (Finset ι × Finset ι)).filter
    (fun p => p.2 ⊆ univ \ p.1
      ∧ sources ends p.1 = (∅ : Finset W)
      ∧ sources ends p.2 = ({o, x} : Finset W)
      ∧ connK ends (p.1 ∪ p.2) x g)


noncomputable def gc48_RHSdoubled (ends : ι → Sym2 W) (o x y g : W) :
    Finset (Finset ι × Finset ι) :=
  (univ : Finset (Finset ι × Finset ι)).filter
    (fun p => p.2 ⊆ univ \ p.1
      ∧ sources ends p.1 = (∅ : Finset W)
      ∧ sources ends p.2 = ({o, x, y, g} : Finset W)
      ∧ connK ends (p.1 ∪ p.2) o x ∧ connK ends (p.1 ∪ p.2) o y ∧ connK ends (p.1 ∪ p.2) o g)


end Abstract
end StatMech.Walls
