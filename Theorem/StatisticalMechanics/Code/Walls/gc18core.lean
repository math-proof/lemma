/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc18core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc16core.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7core
import Theorem.StatisticalMechanics.Code.Walls.gc6_munonneg
import Theorem.StatisticalMechanics.Code.Ising.HdomNativeWeight.Part3
import Theorem.StatisticalMechanics.Code.Ising.AizenmanSignDominance.Part2
import Theorem.StatisticalMechanics.Code.Ising.TwoReplicaWeighted.Part2
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.openClassical false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Sharpness.FieldGhostDict

open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem gc18_star_gap_allConn (β : ℝ) (J : Sym2 V → ℝ) (m' : Ising.Current V) {o x y g : V}
    (hog : o ≠ g) (hox : o ≠ x) (hoy : o ≠ y)
    (Hog : connP (oddEdges G.edgeFinset m') o g)
    (Hox : connP (oddEdges G.edgeFinset m') o x)
    (Hoy : connP (oddEdges G.edgeFinset m') o y) :
    hnw_mass G β J m' ∅ - hnw_mass G β J m' {o, g} - hnw_mass G β J m' {o, x}
        - hnw_mass G β J m' {o, y}
      = -2 * hnw_mass G β J m' ∅ := by
  have e1 : hnw_mass G β J m' {o, g} = hnw_mass G β J m' ∅ := by
    have := hnw_switching G β J m' hog Hog ∅
    rwa [show (∅ : Finset V) ∆ {o, g} = {o, g} from by simp] at this
  have e2 : hnw_mass G β J m' {o, x} = hnw_mass G β J m' ∅ := by
    have := hnw_switching G β J m' hox Hox ∅
    rwa [show (∅ : Finset V) ∆ {o, x} = {o, x} from by simp] at this
  have e3 : hnw_mass G β J m' {o, y} = hnw_mass G β J m' ∅ := by
    have := hnw_switching G β J m' hoy Hoy ∅
    rwa [show (∅ : Finset V) ∆ {o, y} = {o, y} from by simp] at this
  rw [e1, e2, e3]; ring


theorem gc18_star_gap_allConn_nonpos (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (m' : Ising.Current V) {o x y g : V}
    (hog : o ≠ g) (hox : o ≠ x) (hoy : o ≠ y)
    (Hog : connP (oddEdges G.edgeFinset m') o g)
    (Hox : connP (oddEdges G.edgeFinset m') o x)
    (Hoy : connP (oddEdges G.edgeFinset m') o y) :
    hnw_mass G β J m' ∅ - hnw_mass G β J m' {o, g} - hnw_mass G β J m' {o, x}
        - hnw_mass G β J m' {o, y} ≤ 0 := by
  rw [gc18_star_gap_allConn G β J m' hog hox hoy Hog Hox Hoy]
  have := hnw_mass_nonneg G β J hβ hJ m' ∅
  linarith


theorem gc18_star_mass_vanish (β : ℝ) (J : Sym2 V → ℝ) (m' : Ising.Current V)
    (hnd : ∀ e ∈ G.edgeFinset, ¬ e.IsDiag) {u v : V} (huv : u ≠ v)
    (hdisc : ¬ connP (posEdges G.edgeFinset m') u v) :
    hnw_mass G β J m' {u, v} = 0 := by
  unfold hnw_mass splitWeightedSum
  refine Finset.sum_eq_zero (fun K _ => ?_)
  by_cases hKsrc : Sharpness.sources G K.1 = {u, v}
  · exfalso
    apply hdisc
    have hconnOddK : connP (oddEdges G.edgeFinset K.1) u v :=
      connOdd_of_sources G.edgeFinset K.1 hnd huv hKsrc
    have hconnPosK : connP (posEdges G.edgeFinset K.1) u v :=
      connOdd_imp_connPos G.edgeFinset K.1 hconnOddK
    refine connP_mono ?_ hconnPosK
    intro e he
    rw [posEdges, Finset.mem_filter] at he ⊢
    exact ⟨he.1, le_trans he.2 (K.2 e)⟩
  · rw [if_neg hKsrc]


theorem gc18_pair_mass_le_base (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (m' : Ising.Current V) (hnd : ∀ e ∈ G.edgeFinset, ¬ e.IsDiag) {u v : V} (huv : u ≠ v)
    (hreg : connP (oddEdges G.edgeFinset m') u v ∨ ¬ connP (posEdges G.edgeFinset m') u v) :
    hnw_mass G β J m' {u, v} ≤ hnw_mass G β J m' ∅ := by
  rcases hreg with hconn | hdisc
  · 
    have := hnw_switching G β J m' huv hconn ∅
    rw [show (∅ : Finset V) ∆ {u, v} = {u, v} from by simp] at this
    rw [this]
  · 
    rw [gc18_star_mass_vanish G β J m' hnd huv hdisc]
    exact hnw_mass_nonneg G β J hβ hJ m' ∅


theorem gc18_starGap_le_base (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (m' : Ising.Current V) (hnd : ∀ e ∈ G.edgeFinset, ¬ e.IsDiag) {o x y g : V}
    (hog : o ≠ g) (hox : o ≠ x) (hoy : o ≠ y)
    (hg : connP (oddEdges G.edgeFinset m') o g ∨ ¬ connP (posEdges G.edgeFinset m') o g)
    (hx : connP (oddEdges G.edgeFinset m') o x ∨ ¬ connP (posEdges G.edgeFinset m') o x)
    (hy : connP (oddEdges G.edgeFinset m') o y ∨ ¬ connP (posEdges G.edgeFinset m') o y) :
    hnw_mass G β J m' ∅ - hnw_mass G β J m' {o, g} - hnw_mass G β J m' {o, x}
        - hnw_mass G β J m' {o, y}
      ≤ hnw_mass G β J m' ∅ := by
  have b1 := hnw_mass_nonneg G β J hβ hJ m' {o, g}
  have b2 := hnw_mass_nonneg G β J hβ hJ m' {o, x}
  have b3 := hnw_mass_nonneg G β J hβ hJ m' {o, y}
  linarith


theorem gc18_firstFour_reorg (β h : ℝ) (o x y : V) (m : ↥(withGhost G).edgeFinset → ℕ) :
    gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ ∅
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, none}
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some x}
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some y}
      = ∑ K₂ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e},
          (if sources (withGhost G) (ofEdgeFun (withGhost G) K₂.1) = ∅
            then weight (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) K₂.1)
            else 0)
            * (hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1))
                  (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)) ∅
                - hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1))
                    (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)) {some o, none}
                - hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1))
                    (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)) {some o, some x}
                - hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1))
                    (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)) {some o, some y}) := by
  set J' := ghostCoupling h β (fun _ : Sym2 V => (1 : ℝ)) with hJ'
  unfold hnw_mass
  rw [gc16_tpsum_symm (withGhost G) β J' m ∅ {some o, none},
      gc16_tpsum_symm (withGhost G) β J' m ∅ {some o, some x},
      gc16_tpsum_symm (withGhost G) β J' m ∅ {some o, some y},
      gc16_tpsum_bridge (withGhost G) β J' m ∅ ∅,
      gc16_tpsum_bridge (withGhost G) β J' m {some o, none} ∅,
      gc16_tpsum_bridge (withGhost G) β J' m {some o, some x} ∅,
      gc16_tpsum_bridge (withGhost G) β J' m {some o, some y} ∅]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun K₂ _ => ?_)
  ring


theorem gc18_fifth_reorg (β h : ℝ) (o x y : V) (m : ↥(withGhost G).edgeFinset → ℕ) :
    gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m {some o, none} {some x, none}
      = ∑ K₂ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e},
          (if sources (withGhost G) (ofEdgeFun (withGhost G) K₂.1) = {some x, none}
            then weight (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) K₂.1)
            else 0)
            * hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1))
                (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)) {some o, none} := by
  unfold hnw_mass
  exact gc16_tpsum_bridge (withGhost G) β (ghostCoupling h β (fun _ => 1)) m {some o, none}
    {some x, none}


end StatMech.Walls
