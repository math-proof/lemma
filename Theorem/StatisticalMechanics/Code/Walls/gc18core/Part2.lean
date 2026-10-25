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
import Def.StatisticalMechanics.Code.Walls.gc18core
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


theorem gc18_weightedPathCrossing_iff_cert (β h : ℝ) (o x y : V) :
    gc18_WeightedPathCrossing G β h o x y ↔ gc16_PerConfigCert G β h o x y := by
  constructor
  · intro hwpc m hm
    have h4 := gc18_firstFour_reorg G β h o x y m
    have h5 := gc18_fifth_reorg G β h o x y m
    rw [h4, h5]
    exact hwpc m hm
  · intro hcert m hm
    have h4 := gc18_firstFour_reorg G β h o x y m
    have h5 := gc18_fifth_reorg G β h o x y m
    rw [← h4, ← h5]
    exact hcert m hm


theorem gc18_firstFour_nonpos_of_allConn (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hog : (some o : Option V) ≠ none) (hoxs : (some o : Option V) ≠ some x)
    (hoys : (some o : Option V) ≠ some y)
    (m : ↥(withGhost G).edgeFinset → ℕ)
    (hall : ∀ K₂ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e},
        sources (withGhost G) (ofEdgeFun (withGhost G) K₂.1) = ∅ →
        connP (oddEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)))
            (some o) none
          ∧ connP (oddEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)))
              (some o) (some x)
          ∧ connP (oddEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)))
              (some o) (some y)) :
    gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ ∅
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, none}
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some x}
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some y} ≤ 0 := by
  rw [gc18_firstFour_reorg G β h o x y m]
  refine Finset.sum_nonpos (fun K₂ _ => ?_)
  by_cases hK₂ : sources (withGhost G) (ofEdgeFun (withGhost G) K₂.1) = ∅
  · 
    rw [if_pos hK₂]
    obtain ⟨Hog, Hox, Hoy⟩ := hall K₂ hK₂
    rw [gc18_star_gap_allConn (withGhost G) β (ghostCoupling h β (fun _ => 1))
        (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)) hog hoxs hoys Hog Hox Hoy]
    have hJnn : ∀ e, (0 : ℝ) ≤ ghostCoupling h β (fun _ => 1) e :=
      gc6_ghostCoupling_nonneg (V := V) β h hh
    have hw : (0 : ℝ) ≤ weight (withGhost G) β (ghostCoupling h β (fun _ => 1))
        (ofEdgeFun (withGhost G) K₂.1) :=
      asd_weight_nonneg (withGhost G) β (ghostCoupling h β (fun _ => 1)) hβ hJnn _
    have hm0 : (0 : ℝ) ≤ hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1))
        (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)) ∅ :=
      hnw_mass_nonneg (withGhost G) β (ghostCoupling h β (fun _ => 1)) hβ hJnn _ _
    nlinarith [hw, hm0]
  · rw [if_neg hK₂, zero_mul]


theorem gc18_fifth_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x : V)
    (m : ↥(withGhost G).edgeFinset → ℕ) :
    0 ≤ 2 * gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m {some o, none}
        {some x, none} := by
  have hJnn : ∀ e, (0 : ℝ) ≤ ghostCoupling h β (fun _ => 1) e :=
    gc6_ghostCoupling_nonneg (V := V) β h hh
  have := gc16_tpsum_nonneg (withGhost G) β (ghostCoupling h β (fun _ => 1)) hβ hJnn m
    {some o, none} {some x, none}
  linarith


theorem gc18_ursell_nonpos_of_weightedPathCrossing (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hwpc : gc18_WeightedPathCrossing G β h o x y) :
    eg_ursell3 G β h o x y ≤ 0 :=
  gc16_cert_closes_u3 G β h o x y hox hoy hxy
    ((gc18_weightedPathCrossing_iff_cert G β h o x y).mp hwpc)


theorem gc18_ghs_of_weightedPathCrossing (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V)
    (hwpc : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc18_WeightedPathCrossing G β h o x y) :
    GHSThreePointSym G β h o :=
  gc16_ghs_of_cert G β h hβ hh o
    (fun x y hox hoy hxy => (gc18_weightedPathCrossing_iff_cert G β h o x y).mp (hwpc x y hox hoy hxy))


theorem gc18_aizenman_barsky_of_weightedPathCrossing (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (o : V) (J : ℝ)
    (hwpc : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc18_WeightedPathCrossing G β h o x y)
    (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e
        = J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
    bondEnergySusceptibility G β h o
      ≤ J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o :=
  gc16_aizenman_barsky_of_cert G β h hβ hh o J
    (fun x y hox hoy hxy => (gc18_weightedPathCrossing_iff_cert G β h o x y).mp (hwpc x y hox hoy hxy))
    hfactor


theorem gc18_combinatorial_forcing_supplies_starCollapse
    {ι : Type*} [DecidableEq ι] [Fintype ι] (ends : ι → Sym2 V) (K : Finset ι) {o x y g : V}
    (hox : RandomCurrent.connK ends K o x) (hoy : RandomCurrent.connK ends K o y)
    (hog : RandomCurrent.connK ends K o g) :
    RandomCurrent.connK ends K o o ∧ RandomCurrent.connK ends K o x
      ∧ RandomCurrent.connK ends K o y ∧ RandomCurrent.connK ends K o g :=
  gc7_core_allConnected_of_arcs ends K hox hoy hog


theorem gc18_distinct_ursell_nonpos (β h : ℝ) (o : V)
    (hwpc : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc18_WeightedPathCrossing G β h o x y)
    {x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    eg_ursell3 G β h o x y ≤ 0 :=
  gc18_ursell_nonpos_of_weightedPathCrossing G β h o x y hox hoy hxy (hwpc x y hox hoy hxy)

end StatMech.Walls
