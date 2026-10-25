/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc24deltabridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc23allconn.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc22edgecopy.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc15core.Part5
import Theorem.StatisticalMechanics.Code.Walls.gc10deltasupport
import Theorem.StatisticalMechanics.Code.Walls.gc10ensembleprob
import Theorem.StatisticalMechanics.Code.Sharpness.DeltaRewriteDichotomy.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Ising.CurrentWeight.Part2
import Theorem.StatisticalMechanics.Code.Ising.AizenmanSignDominance.Part2
import Def.StatisticalMechanics.Code.Walls.gc24deltabridge
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


theorem gc24_splitWeightedSum_eq_fibreCount (β : ℝ) (J : Sym2 V → ℝ)
    (p : ↥G.edgeFinset → ℕ) (A : Finset V) :
    splitWeightedSum G β J (ofEdgeFun G p) 1 A
      = (gc24_fibreCount G p A : ℝ) * weight G β J (ofEdgeFun G p) :=
  gc22_splitWeightedSum_eq_edgecopy_count G β J p A


theorem gc24_tpsum_eq_fibreCount (β : ℝ) (J : Sym2 V → ℝ) (m : ↥G.edgeFinset → ℕ) (A B : Finset V) :
    gc15_tpsum G β J m A B
      = ∑ K₂ : {K : ↥G.edgeFinset → ℕ // ∀ e, K e ≤ m e},
          (if sources G (ofEdgeFun G K₂.1) = B then weight G β J (ofEdgeFun G K₂.1) else 0)
            * ((gc24_fibreCount G (fun e => m e - K₂.1 e) A : ℝ)
              * weight G β J (ofEdgeFun G (fun e => m e - K₂.1 e))) := by
  rw [gc16_tpsum_bridge G β J m A B]
  refine Finset.sum_congr rfl (fun K₂ _ => ?_)
  rw [gc24_splitWeightedSum_eq_fibreCount G β J (fun e => m e - K₂.1 e) A]


theorem gc24_fibreCount_backbone (p : ↥G.edgeFinset → ℕ) (A : Finset V) {o x y : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hm : RandomCurrent.sources (endsM G p) (univ : Finset (Copy G p)) = A) :
    ((gc24_fibreCount G p A : ℝ)
        - (gc24_fibreCount G p (A ∆ {x, y}) : ℝ)
        - (gc24_fibreCount G p (A ∆ {o, y}) : ℝ)
        - (gc24_fibreCount G p (A ∆ {o, x}) : ℝ))
      = (gc24_fibreCount G p A : ℝ)
        * (1 - (if connK (endsM G p) (univ : Finset (Copy G p)) x y then 1 else 0)
             - (if connK (endsM G p) (univ : Finset (Copy G p)) o y then 1 else 0)
             - (if connK (endsM G p) (univ : Finset (Copy G p)) o x then 1 else 0)) := by
  have h := asd_ghsSigned_eq (endsM G p) (univ : Finset (Copy G p))
    (fun i _ => endsM_not_isDiag G p i) A hm hox hoy hxy (fun _ => (1 : ℝ))
    (fun _ _ _ _ => rfl)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  
  have hpow : ∀ (S : Finset V),
      #((univ : Finset (Finset (Copy G p))).filter
          (fun K => RandomCurrent.sources (endsM G p) K = S))
        = #((univ.powerset : Finset (Finset (Copy G p))).filter
            (fun K => RandomCurrent.sources (endsM G p) K = S)) := by
    intro S; rw [Finset.powerset_univ]
  unfold gc24_fibreCount
  rw [hpow A, hpow (A ∆ {x, y}), hpow (A ∆ {o, y}), hpow (A ∆ {o, x})]
  exact_mod_cast h


theorem gc24_sourcePairDisconnSum_nonneg (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (A B : Finset V) (u v : V) :
    0 ≤ sourcePairDisconnSum G β J A B u v := by
  rw [sourcePairDisconnSum_eq_edgecopy G β J A B u v]
  refine tsum_nonneg (fun m => mul_nonneg (Finset.sum_nonneg (fun S _ => ?_)) ?_)
  · refine mul_nonneg (mul_nonneg ?_ ?_) ?_ <;> positivity
  · exact acw_weight_nonneg G β J hβ hJ _


theorem gc24_switchingGap_nonneg (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (A : Finset V) {u v : V} (huv : u ≠ v) :
    currentSum G β J (A ∆ {u, v}) * currentSum G β J {u, v}
      ≤ currentSum G β J A * currentSum G β J ∅ := by
  have hid := GhostCurrentRep.gcr_currentSum_ghostRep G β J A huv
  have hnn := gc24_sourcePairDisconnSum_nonneg G β J hβ hJ A ∅ u v
  linarith [hid, hnn]


theorem gc24_three_switchingGaps_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ({some o, none} : Finset (Option V))
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
        * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅) := by
  have hJnn : ∀ e, (0 : ℝ) ≤ ghostCoupling h β (fun _ => 1) e :=
    gc6_ghostCoupling_nonneg (V := V) β h hh
  set J' := ghostCoupling h β (fun _ : Sym2 V => (1 : ℝ)) with hJ'
  obtain ⟨dOX, dOY, dOg, dXY, dXg, dYg⟩ := gc15_marks_distinct hox hoy hxy
  refine ⟨?_, ?_, ?_⟩
  · 
    have hg := gc24_switchingGap_nonneg (withGhost G) β J' hβ hJnn
      ({some o, some x, some y, none} : Finset (Option V)) (u := some x) (v := some y) dXY
    have hsd : ({some o, some x, some y, none} : Finset (Option V)) ∆ {some x, some y}
        = {some o, none} := by
      ext a
      simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
      by_cases h1 : a = some o <;> by_cases h2 : a = some x <;> by_cases h3 : a = some y <;>
        by_cases h4 : a = (none : Option V) <;> subst_vars <;> simp_all
    rw [hsd] at hg; exact hg
  · 
    have hg := gc24_switchingGap_nonneg (withGhost G) β J' hβ hJnn
      ({some o, some x, some y, none} : Finset (Option V)) (u := some y) (v := none) (by simp)
    have hsd : ({some o, some x, some y, none} : Finset (Option V)) ∆ {some y, none}
        = {some o, some x} := by
      ext a
      simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
      by_cases h1 : a = some o <;> by_cases h2 : a = some x <;> by_cases h3 : a = some y <;>
        by_cases h4 : a = (none : Option V) <;> subst_vars <;> simp_all
    rw [hsd] at hg; exact hg
  · 
    have hg := gc24_switchingGap_nonneg (withGhost G) β J' hβ hJnn
      ({some o, some x, some y, none} : Finset (Option V)) (u := some x) (v := none) (by simp)
    have hsd : ({some o, some x, some y, none} : Finset (Option V)) ∆ {some x, none}
        = {some o, some y} := by
      ext a
      simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
      by_cases h1 : a = some o <;> by_cases h2 : a = some x <;> by_cases h3 : a = some y <;>
        by_cases h4 : a = (none : Option V) <;> subst_vars <;> simp_all
    rw [hsd] at hg; exact hg


end StatMech.Walls
