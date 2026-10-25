/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc84b_grahamsospositiv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc83crosspairing.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc27polyineq.Part2
import Def.StatisticalMechanics.Code.Walls.gc84b_grahamsospositiv.Part2
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


theorem gc84b_nonneg_combination {ι : Type*} (s : Finset ι) (lam : ι → ℝ) (gen : ι → ℝ)
    (hlam : ∀ i ∈ s, 0 ≤ lam i) (hgen : ∀ i ∈ s, 0 ≤ gen i) :
    0 ≤ ∑ i ∈ s, lam i * gen i :=
  Finset.sum_nonneg (fun i hi => mul_nonneg (hlam i hi) (hgen i hi))


theorem gc84b_no_positivstellensatz : ¬ gc84b_GriffithsConsequence gc84b_ghsResidual := by
  intro hcons
  have hnn := hcons gc84b_parityCorr gc84b_parity_griffiths
  have hneg := gc84b_parity_violates
  linarith


theorem gc84b_griffithsFamily_insufficient :
    ∃ c : Finset (Fin 4) → ℝ,
      gc84b_GriffithsFamily c ∧ ¬ (0 ≤ gc84b_ghsResidual c) :=
  ⟨gc84b_parityCorr, gc84b_parity_griffiths, by have := gc84b_parity_violates; linarith⟩


theorem gc84b_griffiths_sound (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, none}
        * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some x, some y}
      ≤ currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, some x, some y, none}
        * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅)
    ∧ (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, some x}
        * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some y, none}
      ≤ currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, some x, some y, none}
        * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅)
    ∧ (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, some y}
        * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some x, none}
      ≤ currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, some x, some y, none}
        * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅) :=
  gc25_three_switchingGaps_nonneg G β h hβ hh o x y hox hoy hxy


theorem gc84b_residual_closes_ghs (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hpoly : gc27_GHSPolyIneq G β h o x y) :
    eg_ursell3 G β h o x y ≤ 0 :=
  gc27_polyIneq_closes_ghs G β h o x y hox hoy hxy hpoly


theorem gc84b_directSOS_status :
    (gc84b_GriffithsFamily gc84b_parityCorr ∧ gc84b_ghsResidual gc84b_parityCorr < 0)
    ∧ ¬ gc84b_GriffithsConsequence gc84b_ghsResidual
    ∧ (∃ c : Finset (Fin 4) → ℝ, gc84b_GriffithsFamily c ∧ ¬ (0 ≤ gc84b_ghsResidual c)) :=
  ⟨⟨gc84b_parity_griffiths, gc84b_parity_violates⟩,
   gc84b_no_positivstellensatz,
   gc84b_griffithsFamily_insufficient⟩

end StatMech.Walls
