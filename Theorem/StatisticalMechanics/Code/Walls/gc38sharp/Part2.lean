/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc38sharp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc37hdom.Part4
import Def.StatisticalMechanics.Code.Walls.gc38sharp
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

open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.FieldGhostDict


variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

open StatMech.Sharpness (ofEdgeFun weight currentSum sourcePairSum)

open StatMech.Sharpness.FluxEdgeCopy (Copy endsM endsM_not_isDiag sourcePairDisconnSum
  sourcePairDisconnSum_eq_edgecopy sourcePairSum_eq_edgecopy)


theorem gc38_sourcePairAllConnSum_nonneg (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (A : Finset V) (o x y g : V) : 0 ≤ gc38_sourcePairAllConnSum G β J A o x y g := by
  unfold gc38_sourcePairAllConnSum
  refine tsum_nonneg (fun z => ?_)
  refine mul_nonneg (mul_nonneg ?_ ?_) ?_
  · by_cases h : sources G (ofEdgeFun G z.1) = A
    · simp only [h, if_true]; exact acw_weight_nonneg G β J hβ hJ _
    · simp [h]
  · by_cases h : sources G (ofEdgeFun G z.2) = (∅ : Finset V)
    · simp only [h, if_true]; exact acw_weight_nonneg G β J hβ hJ _
    · simp [h]
  · by_cases h : CurrentConnected G (ofEdgeFun G (fun e => z.1 e + z.2 e)) o x
        ∧ CurrentConnected G (ofEdgeFun G (fun e => z.1 e + z.2 e)) o y
        ∧ CurrentConnected G (ofEdgeFun G (fun e => z.1 e + z.2 e)) o g <;> simp [h]


theorem gc38_allConnSum_eq_edgecopy (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) (o x y g : V) :
    gc38_sourcePairAllConnSum G β J A o x y g
      = ∑' m : ↥G.edgeFinset → ℕ,
          (∑ S : Finset (Copy G m),
            (if RandomCurrent.sources (endsM G m) S = A then (1 : ℝ) else 0)
              * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0)
              * (if RandomCurrent.connK (endsM G m) univ o x ∧ RandomCurrent.connK (endsM G m) univ o y
                    ∧ RandomCurrent.connK (endsM G m) univ o g then 1 else 0))
          * weight G β J (ofEdgeFun G m) := by
  classical
  unfold gc38_sourcePairAllConnSum
  rw [FluxEdgeCopy.sourcePairSum_conv_factor G β J A ∅
    (fun m => if CurrentConnected G (ofEdgeFun G m) o x ∧ CurrentConnected G (ofEdgeFun G m) o y
        ∧ CurrentConnected G (ofEdgeFun G m) o g then 1 else 0)
    (fun m => by
      by_cases h : CurrentConnected G (ofEdgeFun G m) o x ∧ CurrentConnected G (ofEdgeFun G m) o y
          ∧ CurrentConnected G (ofEdgeFun G m) o g <;> simp [h])]
  refine tsum_congr (fun m => ?_)
  rw [Finset.sum_mul]
  
  
  rw [show (if CurrentConnected G (ofEdgeFun G m) o x ∧ CurrentConnected G (ofEdgeFun G m) o y
        ∧ CurrentConnected G (ofEdgeFun G m) o g then (1 : ℝ) else 0)
      = (if RandomCurrent.connK (endsM G m) univ o x ∧ RandomCurrent.connK (endsM G m) univ o y
        ∧ RandomCurrent.connK (endsM G m) univ o g then (1 : ℝ) else 0) from by
    rw [FluxEdgeCopy.connK_univ_iff, FluxEdgeCopy.connK_univ_iff, FluxEdgeCopy.connK_univ_iff]]
  by_cases hC : RandomCurrent.connK (endsM G m) univ o x ∧ RandomCurrent.connK (endsM G m) univ o y
      ∧ RandomCurrent.connK (endsM G m) univ o g
  · rw [if_pos hC]
    simp only [mul_one]
    exact FluxEdgeCopy.sourcePair_superposition_bridge G β J A ∅ m
  · rw [if_neg hC]
    simp only [mul_zero, Finset.sum_const_zero, zero_mul]


open StatMech.Sharpness.GhostCurrentRep (gcr_pairCount_empty gcr_pairCount_disconn
  gcr_summable_edgecopy gcr_summable_edgecopy_disconn)


theorem gc38_perSuperposition_assembly (β : ℝ) (J : Sym2 V → ℝ) (m : ↥G.edgeFinset → ℕ)
    {o x y g : V} (hdist : o ≠ x ∧ o ≠ y ∧ o ≠ g ∧ x ≠ y ∧ x ≠ g ∧ y ≠ g) :
    ((∑ S : Finset (Copy G m),
        (if RandomCurrent.sources (endsM G m) S = ({o, x, y, g} : Finset V) then (1 : ℝ) else 0)
          * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0)
          * (if ¬ RandomCurrent.connK (endsM G m) univ x y then 1 else 0))
      + (∑ S : Finset (Copy G m),
          (if RandomCurrent.sources (endsM G m) S = ({o, x, y, g} : Finset V) then (1 : ℝ) else 0)
            * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0)
            * (if ¬ RandomCurrent.connK (endsM G m) univ y g then 1 else 0))
      + (∑ S : Finset (Copy G m),
          (if RandomCurrent.sources (endsM G m) S = ({o, x, y, g} : Finset V) then (1 : ℝ) else 0)
            * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0)
            * (if ¬ RandomCurrent.connK (endsM G m) univ x g then 1 else 0)))
      = 2 * (∑ S : Finset (Copy G m),
          (if RandomCurrent.sources (endsM G m) S = ({o, x, y, g} : Finset V) then (1 : ℝ) else 0)
            * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0))
        - 2 * (∑ S : Finset (Copy G m),
          (if RandomCurrent.sources (endsM G m) S = ({o, x, y, g} : Finset V) then (1 : ℝ) else 0)
            * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0)
            * (if RandomCurrent.connK (endsM G m) univ o x ∧ RandomCurrent.connK (endsM G m) univ o y
                  ∧ RandomCurrent.connK (endsM G m) univ o g then 1 else 0)) := by
  classical
  obtain ⟨hox, hoy, hog, hxy, hxg, hyg⟩ := hdist
  rw [gcr_pairCount_disconn G m ({o, x, y, g} : Finset V) x y,
    gcr_pairCount_disconn G m ({o, x, y, g} : Finset V) y g,
    gcr_pairCount_disconn G m ({o, x, y, g} : Finset V) x g,
    gcr_pairCount_empty G m ({o, x, y, g} : Finset V)]
  
  rw [show (∑ S : Finset (Copy G m),
          (if RandomCurrent.sources (endsM G m) S = ({o, x, y, g} : Finset V) then (1 : ℝ) else 0)
            * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0)
            * (if RandomCurrent.connK (endsM G m) univ o x ∧ RandomCurrent.connK (endsM G m) univ o y
                  ∧ RandomCurrent.connK (endsM G m) univ o g then 1 else 0))
        = (if RandomCurrent.sources (endsM G m) univ = ({o, x, y, g} : Finset V) then (1 : ℝ) else 0)
          * (if RandomCurrent.connK (endsM G m) univ o x ∧ RandomCurrent.connK (endsM G m) univ o y
                ∧ RandomCurrent.connK (endsM G m) univ o g then (1 : ℝ) else 0)
          * (#((univ : Finset (Copy G m)).powerset.filter
              (fun K => RandomCurrent.sources (endsM G m) K = ({o, x, y, g} : Finset V))) : ℝ)
      from by
        rw [show (∑ S : Finset (Copy G m),
              (if RandomCurrent.sources (endsM G m) S = ({o, x, y, g} : Finset V) then (1 : ℝ) else 0)
                * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0)
                * (if RandomCurrent.connK (endsM G m) univ o x ∧ RandomCurrent.connK (endsM G m) univ o y
                      ∧ RandomCurrent.connK (endsM G m) univ o g then 1 else 0))
            = (∑ S : Finset (Copy G m),
                (if RandomCurrent.sources (endsM G m) S = ({o, x, y, g} : Finset V) then (1 : ℝ) else 0)
                  * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0))
              * (if RandomCurrent.connK (endsM G m) univ o x ∧ RandomCurrent.connK (endsM G m) univ o y
                    ∧ RandomCurrent.connK (endsM G m) univ o g then 1 else 0)
          from by rw [Finset.sum_mul]]
        rw [gcr_pairCount_empty G m ({o, x, y, g} : Finset V)]; ring]
  by_cases hAm : RandomCurrent.sources (endsM G m) univ = ({o, x, y, g} : Finset V)
  · rw [if_pos hAm]
    have hsrc : RandomCurrent.sources (endsM G m) univ = ({o, x, y, g} : Finset V) := hAm
    have hparity := gc38_disconn_triple_identity (endsM G m) (univ : Finset (Copy G m))
      (fun i _ => endsM_not_isDiag G m i) ⟨hox, hoy, hog, hxy, hxg, hyg⟩ hsrc
    
    set c : ℝ := (#((univ : Finset (Copy G m)).powerset.filter
        (fun K => RandomCurrent.sources (endsM G m) K = ({o, x, y, g} : Finset V))) : ℝ) with hc
    
    have hneg : (if ¬ (RandomCurrent.connK (endsM G m) univ o x
          ∧ RandomCurrent.connK (endsM G m) univ o y ∧ RandomCurrent.connK (endsM G m) univ o g)
          then (1 : ℝ) else 0)
        = 1 - (if RandomCurrent.connK (endsM G m) univ o x ∧ RandomCurrent.connK (endsM G m) univ o y
              ∧ RandomCurrent.connK (endsM G m) univ o g then 1 else 0) := by
      by_cases h : RandomCurrent.connK (endsM G m) univ o x ∧ RandomCurrent.connK (endsM G m) univ o y
          ∧ RandomCurrent.connK (endsM G m) univ o g <;> simp [h]
    rw [hneg] at hparity
    
    have key := congrArg (fun t => t * c) hparity
    simp only at key
    linarith [key]
  · rw [if_neg hAm]
    simp only [zero_mul, mul_zero, add_zero, sub_zero]


theorem gc38_summable_edgecopy_allConn (β : ℝ) (J : Sym2 V → ℝ) (hJnn : ∀ e, 0 ≤ J e) (hβ : 0 ≤ β)
    (A : Finset V) (o x y g : V) :
    Summable (fun m : ↥G.edgeFinset → ℕ =>
      (∑ S : Finset (Copy G m),
        (if RandomCurrent.sources (endsM G m) S = A then (1 : ℝ) else 0)
          * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0)
          * (if RandomCurrent.connK (endsM G m) univ o x ∧ RandomCurrent.connK (endsM G m) univ o y
                ∧ RandomCurrent.connK (endsM G m) univ o g then 1 else 0))
      * weight G β J (ofEdgeFun G m)) := by
  classical
  have hw : ∀ m : ↥G.edgeFinset → ℕ, 0 ≤ weight G β J (ofEdgeFun G m) := by
    intro m; unfold weight
    refine Finset.prod_nonneg (fun e _ => ?_)
    have hbJ : 0 ≤ β * J e := mul_nonneg hβ (hJnn e); positivity
  refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) (gcr_summable_edgecopy G β J A ∅)
  · 
    apply mul_nonneg _ (hw m)
    refine Finset.sum_nonneg (fun S _ => ?_)
    refine mul_nonneg (mul_nonneg ?_ ?_) ?_
    · by_cases h : RandomCurrent.sources (endsM G m) S = A <;> simp [h]
    · by_cases h : RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) <;> simp [h]
    · by_cases h : RandomCurrent.connK (endsM G m) univ o x ∧ RandomCurrent.connK (endsM G m) univ o y
          ∧ RandomCurrent.connK (endsM G m) univ o g <;> simp [h]
  · 
    apply mul_le_mul_of_nonneg_right _ (hw m)
    refine Finset.sum_le_sum (fun S _ => ?_)
    have hbase : (0 : ℝ) ≤ (if RandomCurrent.sources (endsM G m) S = A then (1 : ℝ) else 0)
        * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0) := by
      refine mul_nonneg ?_ ?_
      · by_cases h : RandomCurrent.sources (endsM G m) S = A <;> simp [h]
      · by_cases h : RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) <;> simp [h]
    by_cases h : RandomCurrent.connK (endsM G m) univ o x ∧ RandomCurrent.connK (endsM G m) univ o y
        ∧ RandomCurrent.connK (endsM G m) univ o g
    · rw [if_pos h, mul_one]
    · rw [if_neg h, mul_zero]; exact hbase


theorem gc38_disconnSum_triple_eq (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    {o x y g : V} (hdist : o ≠ x ∧ o ≠ y ∧ o ≠ g ∧ x ≠ y ∧ x ≠ g ∧ y ≠ g) :
    sourcePairDisconnSum G β J ({o, x, y, g} : Finset V) ∅ x y
      + sourcePairDisconnSum G β J ({o, x, y, g} : Finset V) ∅ y g
      + sourcePairDisconnSum G β J ({o, x, y, g} : Finset V) ∅ x g
      = 2 * sourcePairSum G β J ({o, x, y, g} : Finset V) ∅
        - 2 * gc38_sourcePairAllConnSum G β J ({o, x, y, g} : Finset V) o x y g := by
  classical
  set A : Finset V := {o, x, y, g} with hA
  
  rw [sourcePairDisconnSum_eq_edgecopy G β J A ∅ x y,
    sourcePairDisconnSum_eq_edgecopy G β J A ∅ y g,
    sourcePairDisconnSum_eq_edgecopy G β J A ∅ x g,
    sourcePairSum_eq_edgecopy G β J A ∅,
    gc38_allConnSum_eq_edgecopy G β J A o x y g]
  
  rw [← Summable.tsum_add (gcr_summable_edgecopy_disconn G β J hJ hβ A x y)
        (gcr_summable_edgecopy_disconn G β J hJ hβ A y g),
    ← Summable.tsum_add
        (Summable.add (gcr_summable_edgecopy_disconn G β J hJ hβ A x y)
          (gcr_summable_edgecopy_disconn G β J hJ hβ A y g))
        (gcr_summable_edgecopy_disconn G β J hJ hβ A x g)]
  
  rw [← tsum_mul_left, ← tsum_mul_left,
    ← Summable.tsum_sub
      ((gcr_summable_edgecopy G β J A ∅).mul_left 2)
      ((gc38_summable_edgecopy_allConn G β J hJ hβ A o x y g).mul_left 2)]
  refine tsum_congr (fun m => ?_)
  
  have hassembly := gc38_perSuperposition_assembly G β J m hdist
  
  rw [show (2 : ℝ) * ((∑ S : Finset (Copy G m),
          (if RandomCurrent.sources (endsM G m) S = A then (1 : ℝ) else 0)
            * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0))
        * weight G β J (ofEdgeFun G m))
      - 2 * ((∑ S : Finset (Copy G m),
          (if RandomCurrent.sources (endsM G m) S = A then (1 : ℝ) else 0)
            * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0)
            * (if RandomCurrent.connK (endsM G m) univ o x ∧ RandomCurrent.connK (endsM G m) univ o y
                  ∧ RandomCurrent.connK (endsM G m) univ o g then 1 else 0))
        * weight G β J (ofEdgeFun G m))
      = (2 * (∑ S : Finset (Copy G m),
          (if RandomCurrent.sources (endsM G m) S = A then (1 : ℝ) else 0)
            * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0))
        - 2 * (∑ S : Finset (Copy G m),
          (if RandomCurrent.sources (endsM G m) S = A then (1 : ℝ) else 0)
            * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0)
            * (if RandomCurrent.connK (endsM G m) univ o x ∧ RandomCurrent.connK (endsM G m) univ o y
                  ∧ RandomCurrent.connK (endsM G m) univ o g then 1 else 0)))
        * weight G β J (ofEdgeFun G m) from by ring]
  rw [← hassembly, add_mul, add_mul]


theorem gc38_sd_xy {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) :
    ({some o, some x, some y, none} : Finset (Option V)) ∆ ({some x, some y} : Finset (Option V))
      = ({some o, none} : Finset (Option V)) := by
  ext z; simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (⟨h, hn⟩ | ⟨h, hn⟩) <;> tauto
  · rintro (rfl | rfl) <;> simp_all


theorem gc38_sd_yg {o x y : V} (hoy : o ≠ y) (hxy : x ≠ y) :
    ({some o, some x, some y, none} : Finset (Option V)) ∆ ({some y, none} : Finset (Option V))
      = ({some o, some x} : Finset (Option V)) := by
  ext z; simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (⟨h, hn⟩ | ⟨h, hn⟩) <;> tauto
  · rintro (rfl | rfl) <;> simp_all


theorem gc38_sd_xg {o x y : V} (hox : o ≠ x) (hxy : x ≠ y) :
    ({some o, some x, some y, none} : Finset (Option V)) ∆ ({some x, none} : Finset (Option V))
      = ({some o, some y} : Finset (Option V)) := by
  ext z; simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (⟨h, hn⟩ | ⟨h, hn⟩) <;> tauto
  · rintro (rfl | rfl) <;> simp_all [hxy.symm]


theorem gc38_Z0sq_U4_eq_neg_two_allConn (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    (gc15_Z0 G β h) ^ 2 * gc37_U4 G β h o x y
      = -2 * gc38_sourcePairAllConnSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
          ({some o, some x, some y, none} : Finset (Option V)) (some o) (some x) (some y) none := by
  classical
  set J : Sym2 (Option V) → ℝ := ghostCoupling h β (fun _ => 1) with hJ
  set A : Finset (Option V) := {some o, some x, some y, none} with hA
  have hJnn : ∀ e, (0 : ℝ) ≤ J e := gc6_ghostCoupling_nonneg (V := V) β h hh
  
  have hdist : (some o : Option V) ≠ some x ∧ (some o : Option V) ≠ some y ∧ (some o : Option V) ≠ none
      ∧ (some x : Option V) ≠ some y ∧ (some x : Option V) ≠ none ∧ (some y : Option V) ≠ none := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [hox, hoy, hxy]
  
  have hU4 : (gc15_Z0 G β h) ^ 2 * gc37_U4 G β h o x y
      = (gc15_Z0 G β h) * currentSum (withGhost G) β J
            (insert (none : Option V) (({o, x, y} : Finset V).map someEmb))
        - currentSum (withGhost G) β J (insert (none : Option V) (({o} : Finset V).map someEmb))
            * currentSum (withGhost G) β J (({x, y} : Finset V).map someEmb)
        - currentSum (withGhost G) β J (({o, x} : Finset V).map someEmb)
            * currentSum (withGhost G) β J (insert (none : Option V) (({y} : Finset V).map someEmb))
        - currentSum (withGhost G) β J (({o, y} : Finset V).map someEmb)
            * currentSum (withGhost G) β J (insert (none : Option V) (({x} : Finset V).map someEmb)) :=
    gc37_Z0sq_U4 G β h o x y hox hoy hxy
  simp only [gc15_gsingle, gc15_gpair, gc15_gquad] at hU4
  
  have hZ0 : gc15_Z0 G β h = currentSum (withGhost G) β J ∅ := by rw [gc15_Z0, hJ]
  have g1 := GhostCurrentRep.gcr_currentSum_ghostRep (withGhost G) β J A
      (u := some x) (v := some y) (by simp [hxy])
  have g2 := GhostCurrentRep.gcr_currentSum_ghostRep (withGhost G) β J A
      (u := some y) (v := none) (by simp)
  have g3 := GhostCurrentRep.gcr_currentSum_ghostRep (withGhost G) β J A
      (u := some x) (v := none) (by simp)
  rw [gc38_sd_xy hox hoy] at g1
  rw [gc38_sd_yg hoy hxy] at g2
  rw [gc38_sd_xg hox hxy] at g3
  
  have hparity := gc38_disconnSum_triple_eq (withGhost G) β J hβ hJnn hdist
  
  rw [hU4, hZ0]
  
  have hsps := StatMech.Sharpness.sourcePairSum_eq_mul (withGhost G) β J A ∅
  linarith [g1, g2, g3, hparity, hsps]


theorem gc38_U4_nonpos_unconditional (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    gc37_U4 G β h o x y ≤ 0 := by
  have hid := gc38_Z0sq_U4_eq_neg_two_allConn G β h hβ hh o x y hox hoy hxy
  have hZpos : 0 < gc15_Z0 G β h := gc15_Z0_pos G β h
  have hZ2 : 0 < (gc15_Z0 G β h) ^ 2 := by positivity
  have hJnn : ∀ e, (0 : ℝ) ≤ ghostCoupling h β (fun _ => 1) e :=
    gc6_ghostCoupling_nonneg (V := V) β h hh
  have hconn := gc38_sourcePairAllConnSum_nonneg (withGhost G) β (ghostCoupling h β (fun _ => 1))
    hβ hJnn ({some o, some x, some y, none} : Finset (Option V)) (some o) (some x) (some y) none
  nlinarith [hid, hconn, hZ2]


theorem gc38_U4_nonpos_replaces_connRep_hypothesis (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    gc37_U4 G β h o x y ≤ 0 :=
  gc38_U4_nonpos_unconditional G β h hβ hh o x y hox hoy hxy


end StatMech.Walls
