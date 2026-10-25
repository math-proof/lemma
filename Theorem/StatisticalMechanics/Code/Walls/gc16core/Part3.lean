/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc16core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.MultiReplica.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc15core.Part5
import Theorem.StatisticalMechanics.Code.Ising.AizenmanSignDominance.Part2
import Def.StatisticalMechanics.Code.Walls.gc16core.Part3
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.show false
set_option linter.style.openClassical false
set_option linter.unusedFintypeInType false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Sharpness.FieldGhostDict

open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

variable (S : SimpleGraph V) [DecidableRel S.Adj]


theorem gc16_tpsum_eq_sigma (β : ℝ) (J : Sym2 V → ℝ) (m : ↥S.edgeFinset → ℕ) (A B : Finset V) :
    gc15_tpsum S β J m A B
      = ∑ K₂ : {K : ↥S.edgeFinset → ℕ // ∀ e, K e ≤ m e},
          (if sources S (ofEdgeFun S K₂.1) = B then weight S β J (ofEdgeFun S K₂.1) else 0)
            * (∑ K₁ : {K : ↥S.edgeFinset → ℕ // ∀ e, K e ≤ m e - K₂.1 e},
                (if sources S (ofEdgeFun S K₁.1) = A then weight S β J (ofEdgeFun S K₁.1) else 0)
                  * weight S β J (ofEdgeFun S (fun e => (m e - K₂.1 e) - K₁.1 e))) := by
  unfold gc15_tpsum
  rw [Fintype.sum_equiv (gc16_splitSigmaEquiv S m) _
    (fun s : Σ K₂ : {K : ↥S.edgeFinset → ℕ // ∀ e, K e ≤ m e},
        {K : ↥S.edgeFinset → ℕ // ∀ e, K e ≤ m e - K₂.1 e} =>
      (if sources S (ofEdgeFun S s.1.1) = B then weight S β J (ofEdgeFun S s.1.1) else 0)
      * ((if sources S (ofEdgeFun S s.2.1) = A then weight S β J (ofEdgeFun S s.2.1) else 0)
          * weight S β J (ofEdgeFun S (fun e => (m e - s.1.1 e) - s.2.1 e))))]
  · rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl (fun K₂ _ => ?_)
    rw [Finset.mul_sum]
  · intro K
    simp only [gc16_splitSigmaEquiv, Equiv.coe_fn_mk]
    have hsub : (fun e => m e - K.1.2 e - K.1.1 e) = (fun e => m e - K.1.1 e - K.1.2 e) := by
      ext e; omega
    rw [hsub]; ring


theorem gc16_tpsum_bridge (β : ℝ) (J : Sym2 V → ℝ) (m : ↥S.edgeFinset → ℕ) (A B : Finset V) :
    gc15_tpsum S β J m A B
      = ∑ K₂ : {K : ↥S.edgeFinset → ℕ // ∀ e, K e ≤ m e},
          (if sources S (ofEdgeFun S K₂.1) = B then weight S β J (ofEdgeFun S K₂.1) else 0)
            * splitWeightedSum S β J (ofEdgeFun S (fun e => m e - K₂.1 e)) 1 A := by
  rw [gc16_tpsum_eq_sigma S β J m A B]
  refine Finset.sum_congr rfl (fun K₂ _ => ?_)
  congr 1
  rw [← gc16_inner_eq_splitWeightedSum S β J (fun e => m e - K₂.1 e) A]


theorem gc16_threeGap_eq_gated (β h : ℝ) (o x y : V) (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (m : ↥(withGhost G).edgeFinset → ℕ)
    (hm : sources (withGhost G) (ofEdgeFun (withGhost G) m)
        = ({some o, some x, some y, none} : Finset (Option V))) :
    gc15_threeGap G β h o x y m
      = gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ ∅
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, none}
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some x}
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some y}
        + 2 * gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m
              {some o, none} {some x, none} := by
  obtain ⟨dOX, dOY, dOg, dXY, dXg, dYg⟩ := gc15_marks_distinct hox hoy hxy
  unfold gc15_threeGap gc15_tFiber
  rw [gc15_sd0 (some o) (some x) (some y) none,
      gc15_sd1 (some o) (some x) (some y) none dOX dOY dOg dXY dXg dYg,
      gc15_sd2 (some o) (some x) (some y) none dOX dOY dOg dXY dXg dYg,
      gc15_sd3 (some o) (some x) (some y) none dOX dOY dOg dXY dXg dYg,
      gc15_sd4 (some o) (some x) (some y) none dOX dOY dOg dXY dXg dYg]
  rw [if_pos hm, if_pos hm, if_pos hm, if_pos hm, if_pos hm]


theorem gc16_perConfig_off_boundary (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (m : ↥(withGhost G).edgeFinset → ℕ)
    (hm : sources (withGhost G) (ofEdgeFun (withGhost G) m)
        ≠ ({some o, some x, some y, none} : Finset (Option V))) :
    gc15_threeGap G β h o x y m ≤ 0 := by
  rw [gc15_threeGap_vanish G β h o x y hox hoy hxy m hm]


end StatMech.Walls
