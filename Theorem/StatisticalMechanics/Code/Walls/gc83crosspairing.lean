/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc83crosspairing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc82grahamgeometric.Part2
import Instance.StatisticalMechanics.Code.Walls.gc83crosspairing
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


theorem gc83_threeGap_eq_fam (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (m : ↥(withGhost G).edgeFinset → ℕ) :
    gc15_threeGap G β h o x y m
      = (if gc83_fourMark G o x y m then gc83_fam1 G β h o x y m + 2 * gc83_fam2 G β h o x y m
          else 0) := by
  obtain ⟨dOX, dOY, dOg, dXY, dXg, dYg⟩ := gc15_marks_distinct hox hoy hxy
  unfold gc15_threeGap gc83_fam1 gc83_fam2 gc83_fourMark
  
  unfold gc15_tFiber
  rw [gc15_sd0 (some o) (some x) (some y) none,
      gc15_sd1 (some o) (some x) (some y) none dOX dOY dOg dXY dXg dYg,
      gc15_sd2 (some o) (some x) (some y) none dOX dOY dOg dXY dXg dYg,
      gc15_sd3 (some o) (some x) (some y) none dOX dOY dOg dXY dXg dYg,
      gc15_sd4 (some o) (some x) (some y) none dOX dOY dOg dXY dXg dYg]
  by_cases hm : sources (withGhost G) (ofEdgeFun (withGhost G) m)
      = ({some o, some x, some y, none} : Finset (Option V))
  · simp only [if_pos hm]
  · simp only [if_neg hm]; ring


theorem gc83_threeGap_zero_off_fourMark (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (m : ↥(withGhost G).edgeFinset → ℕ) (hm : ¬ gc83_fourMark G o x y m) :
    gc15_threeGap G β h o x y m = 0 := by
  rw [gc83_threeGap_eq_fam G β h o x y hox hoy hxy m, if_neg hm]


theorem gc83_ghostCoupling_nonneg (β h : ℝ) (hh : 0 ≤ h) :
    ∀ e : Sym2 (Option V), 0 ≤ ghostCoupling h β (fun _ => (1 : ℝ)) e := by
  intro e
  refine Sym2.ind (fun a b => ?_) e
  match a, b with
  | some p, some q => simp
  | some p, none => simpa using hh
  | none, some q => simpa [ghostCoupling] using hh
  | none, none => simp [ghostCoupling]


theorem gc83_weight_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (n : Sharpness.Current (Option V)) :
    0 ≤ weight (withGhost G) β (ghostCoupling h β (fun _ => (1 : ℝ))) n := by
  unfold weight
  refine Finset.prod_nonneg (fun e _ => ?_)
  exact div_nonneg
    (pow_nonneg (mul_nonneg hβ (gc83_ghostCoupling_nonneg (V := V) β h hh e)) _) (by positivity)


theorem gc83_fam2_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (m : ↥(withGhost G).edgeFinset → ℕ) :
    0 ≤ gc83_fam2 G β h o x y m := by
  unfold gc83_fam2 gc15_tpsum
  refine Finset.sum_nonneg (fun K _ => ?_)
  have h1 : 0 ≤ (if sources (withGhost G) (ofEdgeFun (withGhost G) K.1.1) = {some o, none}
        then weight (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) K.1.1)
        else 0) := by
    split
    · exact gc83_weight_nonneg G β h hβ hh _
    · exact le_refl 0
  have h2 : 0 ≤ (if sources (withGhost G) (ofEdgeFun (withGhost G) K.1.2) = {some x, none}
        then weight (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) K.1.2)
        else 0) := by
    split
    · exact gc83_weight_nonneg G β h hβ hh _
    · exact le_refl 0
  have h3 : 0 ≤ weight (withGhost G) β (ghostCoupling h β (fun _ => 1))
        (ofEdgeFun (withGhost G) (fun e => m e - K.1.1 e - K.1.2 e)) :=
    gc83_weight_nonneg G β h hβ hh _
  exact mul_nonneg (mul_nonneg h1 h2) h3


end StatMech.Walls
