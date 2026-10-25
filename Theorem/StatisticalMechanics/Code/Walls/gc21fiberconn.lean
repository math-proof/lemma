/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc21fiberconn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc20closure.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc19switching.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc18core.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc16core.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7core
import Theorem.StatisticalMechanics.Code.Walls.gc6_munonneg
import Theorem.StatisticalMechanics.Code.Ising.TwoReplica.Part7
import Theorem.StatisticalMechanics.Code.Ising.TwoReplicaWeighted.Part2
import Theorem.StatisticalMechanics.Code.Ising.HdomNativeWeight.Part3
import Theorem.StatisticalMechanics.Code.Ising.AizenmanSignDominance.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Def.StatisticalMechanics.Code.Walls.gc21fiberconn
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

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Sharpness.RandomCurrent StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.FieldGhostDict


theorem gc21_oddFibre_not_of_posFull :
    connP (posEdges gc21_E2 gc21_m2) 0 1 ∧ ¬ connP (oddEdges gc21_E2 gc21_m2) 0 1 := by
  refine ⟨?_, ?_⟩
  · 
    refine Relation.ReflTransGen.single ⟨s(0, 1), ?_, by simp, by simp, by decide⟩
    rw [posEdges, Finset.mem_filter]
    refine ⟨by rw [gc21_E2]; simp, ?_⟩
    show 1 ≤ gc21_m2 s(0, 1)
    simp only [gc21_m2]; decide
  · 
    intro h
    have hempty : oddEdges gc21_E2 gc21_m2 = ∅ := by
      rw [oddEdges]
      apply Finset.filter_eq_empty_iff.mpr
      intro e he
      rw [gc21_E2, Finset.mem_singleton] at he
      subst he
      show ¬ Odd (gc21_m2 s(0, 1))
      simp only [gc21_m2]; decide
    rw [hempty] at h
    cases h with
    | tail _ hstep =>
      obtain ⟨e, he, _, _, _⟩ := hstep
      exact absurd he (by simp)


end StatMech.Walls
