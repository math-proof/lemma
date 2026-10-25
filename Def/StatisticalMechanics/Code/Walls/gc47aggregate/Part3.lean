/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc47aggregate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc46redistribute.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc47aggregate.Part2
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

def gc47_defectΦ : (Σ _ : Finset (Fin 5), Finset (Fin 5)) → (Σ _ : Finset (Fin 5), Finset (Fin 5)) :=
  fun p =>
    if p.1 = ({3, 4} : Finset (Fin 5)) ∧ p.2 = (∅ : Finset (Fin 5)) then ⟨univ, ∅⟩
    else if p.1 = ({0, 1, 3, 4} : Finset (Fin 5)) ∧ p.2 = (∅ : Finset (Fin 5)) then ⟨{0, 3, 4}, ∅⟩
    else if p.1 = ({0, 2, 3, 4} : Finset (Fin 5)) ∧ p.2 = (∅ : Finset (Fin 5)) then ⟨{1, 3, 4}, ∅⟩
    else if p.1 = ({1, 2, 3, 4} : Finset (Fin 5)) ∧ p.2 = (∅ : Finset (Fin 5)) then ⟨{2, 3, 4}, ∅⟩
    else if p.1 = ({0, 1, 3, 4} : Finset (Fin 5)) ∧ p.2 = ({0, 1} : Finset (Fin 5)) then ⟨univ, {0, 1}⟩
    else if p.1 = ({0, 2, 3, 4} : Finset (Fin 5)) ∧ p.2 = ({0, 2} : Finset (Fin 5)) then ⟨univ, {0, 2}⟩
    else ⟨univ, {1, 2}⟩


end StatMech.Walls
