/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.Switching.Part3
import Def.StatisticalMechanics.Code.Walls.menger_core
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

open StatMech.Sharpness.RandomCurrent (sources connK connK_symm adjStep degK compOf
  sources_symmDiff mem_sources path_exists exists_conn_set)

open Classical


theorem mng_cyc_loopless : ∀ i : Fin 4, ¬ (mng_cyc i).IsDiag := by decide


theorem mng_cyc_univ_sources : sources mng_cyc (univ : Finset (Fin 4)) = (∅ : Finset (Fin 4)) := by
  decide


theorem mng_cyc_P1_sources :
    sources mng_cyc ({0, 1} : Finset (Fin 4)) = ({0, 2} : Finset (Fin 4)) := by decide


theorem mng_cyc_P2_sources :
    sources mng_cyc ({2, 3} : Finset (Fin 4)) = ({0, 2} : Finset (Fin 4)) := by decide


theorem mng_cyc_disjoint : Disjoint ({0, 1} : Finset (Fin 4)) ({2, 3} : Finset (Fin 4)) := by decide


theorem mng_cyc_P1_conn : connK mng_cyc ({0, 1} : Finset (Fin 4)) 0 2 :=
  (Relation.ReflTransGen.single (b := (1 : Fin 4))
      ⟨0, by decide, by decide, by decide, by decide⟩).trans
    (Relation.ReflTransGen.single (b := (2 : Fin 4))
      ⟨1, by decide, by decide, by decide, by decide⟩)


theorem mng_cyc_P2_conn : connK mng_cyc ({2, 3} : Finset (Fin 4)) 0 2 :=
  (Relation.ReflTransGen.single (b := (3 : Fin 4))
      ⟨3, by decide, by decide, by decide, by decide⟩).trans
    (Relation.ReflTransGen.single (b := (2 : Fin 4))
      ⟨2, by decide, by decide, by decide, by decide⟩)


theorem mng_test_cycle_two_disjoint :
    ∃ P₁ P₂ : Finset (Fin 4),
      P₁ ⊆ (univ : Finset (Fin 4)) ∧ P₂ ⊆ (univ : Finset (Fin 4)) ∧ Disjoint P₁ P₂ ∧
      sources mng_cyc P₁ = ({0, 2} : Finset (Fin 4)) ∧
      sources mng_cyc P₂ = ({0, 2} : Finset (Fin 4)) ∧
      connK mng_cyc P₁ 0 2 ∧ connK mng_cyc P₂ 0 2 :=
  ⟨{0, 1}, {2, 3}, Finset.subset_univ _, Finset.subset_univ _, mng_cyc_disjoint,
    mng_cyc_P1_sources, mng_cyc_P2_sources, mng_cyc_P1_conn, mng_cyc_P2_conn⟩


end StatMech.Walls
