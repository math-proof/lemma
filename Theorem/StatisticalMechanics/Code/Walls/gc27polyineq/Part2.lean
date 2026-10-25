/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc27polyineq.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc25resummation.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc24deltabridge.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc15core.Part5
import Def.StatisticalMechanics.Code.Walls.gc27polyineq.Part2
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

open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem gc27_threeUsedGaps_in_family (a b c r q p t : ℝ)
    (hfam : gc27_TwoSourceGapFamily a b c r q p t) :
    a * p ≤ t ∧ b * q ≤ t ∧ c * r ≤ t :=
  hfam.2.2.1


theorem gc27_twoSourceGaps_insufficient :
    ∃ a b c r q p t : ℝ,
      gc27_TwoSourceGapFamily a b c r q p t
        ∧ ¬ (t + 2 * (a * b * c) ≤ a * p + b * q + c * r) := by
  refine ⟨0, 0, 0, 0, 0, 0, 1, ?_, ?_⟩
  · refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩,
      ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;> norm_num
  · norm_num


theorem gc27_tripleBound_not_from_family :
    ∃ a b c r q p t : ℝ,
      gc27_TwoSourceGapFamily a b c r q p t
        ∧ ¬ (2 * (a * b * c) ≤ a * p + b * q + c * r - t) := by
  refine ⟨0, 0, 0, 0, 0, 0, 1, ?_, ?_⟩
  · refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩,
      ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;> norm_num
  · norm_num


theorem gc27_three_switchingGaps_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, none}
        * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some x, some y}
      ≤ currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
          {some o, some x, some y, none}
        * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅)
    ∧ (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, some x}
        * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some y, none}
      ≤ currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
          {some o, some x, some y, none}
        * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅)
    ∧ (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, some y}
        * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some x, none}
      ≤ currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
          {some o, some x, some y, none}
        * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅) :=
  gc25_three_switchingGaps_nonneg G β h hβ hh o x y hox hoy hxy


theorem gc27_obstruction_named (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    (gc27_GHSPolyIneq G β h o x y ↔ eg_ursell3 G β h o x y ≤ 0)
      ∧ (gc25_NativeResummation G β h o x y → gc27_GHSPolyIneq G β h o x y)
      ∧ (∃ a b c r q p t : ℝ, gc27_TwoSourceGapFamily a b c r q p t
          ∧ ¬ (t + 2 * (a * b * c) ≤ a * p + b * q + c * r)) :=
  ⟨(gc27_ghs_iff_polyIneq G β h o x y hox hoy hxy).symm,
   gc27_polyIneq_of_nativeResummation G β h hβ hh o x y hox hoy hxy,
   gc27_twoSourceGaps_insufficient⟩

end StatMech.Walls
