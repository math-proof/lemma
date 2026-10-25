/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_general.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.menger_core.Part3
import Def.StatisticalMechanics.Code.Walls.menger_general.Part5
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


theorem mngg_theta_loopless : ∀ i : Fin 6, ¬ (mngg_theta i).IsDiag := by decide


theorem mngg_theta_P1_sources :
    sources mngg_theta ({0} : Finset (Fin 6)) = ({0, 4} : Finset (Fin 5)) := by decide


theorem mngg_theta_P2_sources :
    sources mngg_theta ({1, 2} : Finset (Fin 6)) = ({0, 4} : Finset (Fin 5)) := by decide


theorem mngg_theta_P3_sources :
    sources mngg_theta ({3, 4, 5} : Finset (Fin 6)) = ({0, 4} : Finset (Fin 5)) := by decide


theorem mngg_theta_disjoint :
    Disjoint ({0} : Finset (Fin 6)) ({1, 2} : Finset (Fin 6)) ∧
    Disjoint ({0} : Finset (Fin 6)) ({3, 4, 5} : Finset (Fin 6)) ∧
    Disjoint ({1, 2} : Finset (Fin 6)) ({3, 4, 5} : Finset (Fin 6)) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide


theorem mngg_theta_P1_conn : connK mngg_theta ({0} : Finset (Fin 6)) 0 4 :=
  Relation.ReflTransGen.single (b := (4 : Fin 5))
    ⟨0, by decide, by decide, by decide, by decide⟩


theorem mngg_theta_P2_conn : connK mngg_theta ({1, 2} : Finset (Fin 6)) 0 4 :=
  (Relation.ReflTransGen.single (b := (1 : Fin 5))
      ⟨1, by decide, by decide, by decide, by decide⟩).trans
    (Relation.ReflTransGen.single (b := (4 : Fin 5))
      ⟨2, by decide, by decide, by decide, by decide⟩)


theorem mngg_theta_P3_conn : connK mngg_theta ({3, 4, 5} : Finset (Fin 6)) 0 4 :=
  (Relation.ReflTransGen.single (b := (2 : Fin 5))
      ⟨3, by decide, by decide, by decide, by decide⟩).trans
    ((Relation.ReflTransGen.single (b := (3 : Fin 5))
        ⟨4, by decide, by decide, by decide, by decide⟩).trans
      (Relation.ReflTransGen.single (b := (4 : Fin 5))
        ⟨5, by decide, by decide, by decide, by decide⟩))


theorem mngg_test_theta_three_disjoint :
    ∃ P₁ P₂ P₃ : Finset (Fin 6),
      P₁ ⊆ (univ : Finset (Fin 6)) ∧ P₂ ⊆ (univ : Finset (Fin 6)) ∧ P₃ ⊆ (univ : Finset (Fin 6)) ∧
      Disjoint P₁ P₂ ∧ Disjoint P₁ P₃ ∧ Disjoint P₂ P₃ ∧
      sources mngg_theta P₁ = ({0, 4} : Finset (Fin 5)) ∧
      sources mngg_theta P₂ = ({0, 4} : Finset (Fin 5)) ∧
      sources mngg_theta P₃ = ({0, 4} : Finset (Fin 5)) ∧
      connK mngg_theta P₁ 0 4 ∧ connK mngg_theta P₂ 0 4 ∧ connK mngg_theta P₃ 0 4 :=
  ⟨{0}, {1, 2}, {3, 4, 5}, Finset.subset_univ _, Finset.subset_univ _, Finset.subset_univ _,
    mngg_theta_disjoint.1, mngg_theta_disjoint.2.1, mngg_theta_disjoint.2.2,
    mngg_theta_P1_sources, mngg_theta_P2_sources, mngg_theta_P3_sources,
    mngg_theta_P1_conn, mngg_theta_P2_conn, mngg_theta_P3_conn⟩


theorem mngg_test_residual_conn :
    connK mngg_theta ((univ : Finset (Fin 6)) \ ({0, 1, 2} : Finset (Fin 6))) 0 4 := by
  have hsub : ({3, 4, 5} : Finset (Fin 6)) ⊆ (univ : Finset (Fin 6)) \ ({0, 1, 2} : Finset (Fin 6)) := by
    decide
  exact mng_connK_mono mngg_theta hsub mngg_theta_P3_conn


end StatMech.Walls
