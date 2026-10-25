/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/FaithfulnessAudit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.Ising.AizenmanBarsky.Part5
import Theorem.StatisticalMechanics.Code.Walls.ghc_urselleqgap
import Theorem.StatisticalMechanics.Code.Walls.gc31surgery.Part3
import Theorem.StatisticalMechanics.Code.Ising.BackboneResummation.Part2
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Percolation.RootedForestPeelClose.Part4
import Theorem.StatisticalMechanics.Code.Walls.bc28forestroot.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.Reimer.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompression.Part5
import Theorem.StatisticalMechanics.Code.Walls.rc18nonmono.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc19doublecover.Part4
import Def.StatisticalMechanics.Code.Walls.FaithfulnessAudit.Part2
open scoped BigOperators
open Finset SimpleGraph
open StatMech StatMech.Ising StatMech.Walls.GhcEqGap
open StatMech.Lattice StatMech.Percolation


namespace StatMech.Walls

set_option linter.unusedSectionVars false

set_option maxHeartbeats 800000


variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


variable {d : ℕ}


theorem fa_reimer_parA_not_increasing : ¬ StatMech.IsIncreasing fa_reimer_parA := by
  intro hinc
  have h1 : (fun _ => false) ∈ fa_reimer_parA := by simp [fa_reimer_parA]
  have hle : (fun _ => false : ConfigSpace (Fin 4)) ≤ (fun i => if i = 0 then true else false) := by
    intro i; simp only; split <;> simp [Bool.le_iff_imp]
  have h2 := hinc hle h1
  simp only [fa_reimer_parA, Set.mem_setOf_eq] at h2
  revert h2; decide


theorem fa_reimer_target_true_nonmonotone (φ : Fin 4 → Bool → ℝ)
    (hφ1 : ∀ i, φ i false + φ i true = 1) :
    StatMech.wprob φ (StatMech.disjointOccurrence fa_reimer_parA fa_reimer_parB)
      = StatMech.wprob φ fa_reimer_parA * StatMech.wprob φ fa_reimer_parB := by
  have hA : StatMech.DependsOn fa_reimer_parA ({0, 1} : Set (Fin 4)) := by
    intro ω ω' hag
    simp only [fa_reimer_parA, Set.mem_setOf_eq]
    rw [hag 0 (by simp), hag 1 (by simp)]
  have hB : StatMech.DependsOn fa_reimer_parB ({2, 3} : Set (Fin 4)) := by
    intro ω ω' hag
    simp only [fa_reimer_parB, Set.mem_setOf_eq]
    rw [hag 2 (by simp), hag 3 (by simp)]
  have hST : Disjoint ({0, 1} : Set (Fin 4)) ({2, 3} : Set (Fin 4)) := by
    rw [Set.disjoint_left]; intro x hx hx'; fin_cases x <;> simp_all
  exact StatMech.reimer_wprob_of_disjoint_support φ hφ1 hA hB hST


theorem fa_reimer_naive_familyBKR_false :
    ¬ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))),
        #(rc10_boxSupp 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ)) :=
  rc18_familyBKR_false


theorem fa_reimer_residue_iff_wall :
    rc18_CylBoxReflInter ↔ rc17_NonMonotoneDeficit :=
  rc18_cylBoxReflInter_iff_nonMonotone


theorem fa_reimer_residue_nonvacuous :
    ((¬ StatMech.IsIncreasing rbi_A ∧ ¬ StatMech.IsDecreasing rbi_A)
        ∨ (¬ StatMech.IsIncreasing rbi_B ∧ ¬ StatMech.IsDecreasing rbi_B))
      ∧ #(rc18_cylBoxSupp rbi_A rbi_B)
          ≤ #(rc10_reflInter (eventFamily rbi_A) (eventFamily rbi_B)) :=
  rc18_cylBoxReflInter_rbi


theorem fa_reimer_target_of_residue (h : rc18_CylBoxReflInter) : ReimerWprobCore :=
  rc18_reimerWprobCore_of_cylBoxReflInter h

end StatMech.Walls
