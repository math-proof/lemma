/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeParityLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.GeneralInteractionFreeSpinLimit.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.InhomogeneousParityAvoidance.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.PlusBoxCurrentParity.Part3
import Def.StatisticalMechanics.Code.FrontierB.GeneralInteractionFreeParityLimit.Part6
open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal symmDiff


namespace StatMech.FrontierB

open Sharpness Ising Lattice

theorem preimage_currentParityAvoidCylinder_nonDiagonal
    (d n : Nat) (F : Finset (Sym2 (Site d))) :
    extendInteractionBoxCurrent d n ⁻¹' currentParityAvoidCylinder F =
      extendInteractionBoxCurrent d n ⁻¹'
        currentParityAvoidCylinder (nonDiagonalEdgeFinset F) := by
  ext m
  simp only [Set.mem_preimage, currentParityAvoidCylinder,
    nonDiagonalEdgeFinset, Finset.mem_filter]
  constructor
  · intro h e heF
    exact h e heF.1
  · intro h e heF
    by_cases he : e.IsDiag
    · rw [extendInteractionBoxCurrent_diag_zero d n m e he]
      norm_num
    · exact h e ⟨heF, he⟩

theorem generalFreeBoxCurrentMeasure_parityAvoid_nonDiagonal
    {d : Nat} (J : Sym2 (Site d) → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (beta : ℝ) (hbeta : 0 ≤ beta) (n : Nat)
    (F : Finset (Sym2 (Site d))) :
    (generalFreeBoxCurrentMeasure J hJ n beta hbeta :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        (currentParityAvoidCylinder F) =
      (generalFreeBoxCurrentMeasure J hJ n beta hbeta :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        (currentParityAvoidCylinder (nonDiagonalEdgeFinset F)) := by
  have hmeasF := measurableSet_currentParityAvoidCylinder F
  have hmeasD := measurableSet_currentParityAvoidCylinder
    (nonDiagonalEdgeFinset F)
  change Measure.map (extendInteractionBoxCurrent d n)
      ((sourcelessCurrentPMF (interactionBoxGraph d n) beta
        (interactionBoxCoupling J n) hbeta
          (fun e => hJ (Sym2.map Subtype.val e))).toMeasure)
        (currentParityAvoidCylinder F) =
    Measure.map (extendInteractionBoxCurrent d n)
      ((sourcelessCurrentPMF (interactionBoxGraph d n) beta
        (interactionBoxCoupling J n) hbeta
          (fun e => hJ (Sym2.map Subtype.val e))).toMeasure)
        (currentParityAvoidCylinder (nonDiagonalEdgeFinset F))
  rw [Measure.map_apply (measurable_extendInteractionBoxCurrent d n) hmeasF,
    Measure.map_apply (measurable_extendInteractionBoxCurrent d n) hmeasD,
    preimage_currentParityAvoidCylinder_nonDiagonal]


theorem generalFreeBoxCurrentMeasure_parityAvoid_full_tendsto_all {d : Nat}
    (J : Sym2 (Site d) → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (beta : ℝ) (hbeta : 0 < beta)
    (F : Finset (Sym2 (Site d))) :
    ∃ L : ℝ≥0∞, Tendsto
      (fun n => (generalFreeBoxCurrentMeasure J hJ n beta hbeta.le :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))
          (currentParityAvoidCylinder F)) atTop (nhds L) := by
  let D := nonDiagonalEdgeFinset F
  have hDdiag : ∀ e ∈ D, ¬e.IsDiag := by
    intro e he
    exact (Finset.mem_filter.mp he).2
  obtain ⟨L, hL⟩ := generalFreeBoxCurrentMeasure_parityAvoid_full_tendsto
    J hJ beta hbeta D hDdiag
  refine ⟨L, hL.congr' ?_⟩
  filter_upwards [] with n
  exact (generalFreeBoxCurrentMeasure_parityAvoid_nonDiagonal
    J hJ beta hbeta.le n F).symm

end StatMech.FrontierB
