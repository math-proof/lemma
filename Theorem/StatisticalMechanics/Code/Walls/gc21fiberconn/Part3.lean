/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc21fiberconn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc20closure.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc19switching.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc18core.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc16core.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7core
import Theorem.StatisticalMechanics.Code.Walls.gc6_munonneg
import Theorem.StatisticalMechanics.Code.Ising.TwoReplica.Part7
import Theorem.StatisticalMechanics.Code.Ising.TwoReplicaWeighted.Part2
import Theorem.StatisticalMechanics.Code.Ising.HdomNativeWeight.Part3
import Theorem.StatisticalMechanics.Code.Ising.AizenmanSignDominance.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Def.StatisticalMechanics.Code.Walls.gc21fiberconn.Part3
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


variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem gc21_allConn_oddArcs_of_bridge (m : ↥(withGhost G).edgeFinset → ℕ)
    (hbridge : gc21_FibreOddArcBridge G m)
    (K₁ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e}) (o x y g : Option V)
    (hposOg : connP (posEdges (withGhost G).edgeFinset
        (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) o g)
    (hposOx : connP (posEdges (withGhost G).edgeFinset
        (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) o x)
    (hposOy : connP (posEdges (withGhost G).edgeFinset
        (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) o y) :
    connP (oddEdges (withGhost G).edgeFinset
          (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) o g
      ∧ connP (oddEdges (withGhost G).edgeFinset
          (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) o x
      ∧ connP (oddEdges (withGhost G).edgeFinset
          (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) o y :=
  ⟨hbridge K₁ o g hposOg, hbridge K₁ o x hposOx, hbridge K₁ o y hposOy⟩


theorem gc21_fibre_starGap_nonpos_of_bridge (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (m : ↥(withGhost G).edgeFinset → ℕ) (hbridge : gc21_FibreOddArcBridge G m)
    (K₁ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e})
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hbdry : sources (withGhost G) (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))
        = ({some o, some x, some y, none} : Finset (Option V))) :
    hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1))
          (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e)) ∅
      - hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1))
          (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e)) {some o, none}
      - hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1))
          (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e)) {some o, some x}
      - hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1))
          (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e)) {some o, some y} ≤ 0 := by
  have hog : (some o : Option V) ≠ none := by simp
  have hoxs : (some o : Option V) ≠ some x := by simpa using hox
  have hoys : (some o : Option V) ≠ some y := by simpa using hoy
  have hxys : (some x : Option V) ≠ some y := by simpa using hxy
  have hxgs : (some x : Option V) ≠ none := by simp
  have hygs : (some y : Option V) ≠ none := by simp
  set fib := ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e) with hfib
  set J' := ghostCoupling h β (fun _ : Sym2 V => (1 : ℝ)) with hJ'
  have hJnn : ∀ e, (0 : ℝ) ≤ J' e := gc6_ghostCoupling_nonneg (V := V) β h hh
  have bg : 0 ≤ hnw_mass (withGhost G) β J' fib {some o, none} :=
    hnw_mass_nonneg (withGhost G) β J' hβ hJnn fib _
  have bx : 0 ≤ hnw_mass (withGhost G) β J' fib {some o, some x} :=
    hnw_mass_nonneg (withGhost G) β J' hβ hJnn fib _
  have by' : 0 ≤ hnw_mass (withGhost G) β J' fib {some o, some y} :=
    hnw_mass_nonneg (withGhost G) β J' hβ hJnn fib _
  have b0 : 0 ≤ hnw_mass (withGhost G) β J' fib ∅ :=
    hnw_mass_nonneg (withGhost G) β J' hβ hJnn fib _
  have collapse : ∀ (a : Option V), (some o : Option V) ≠ a →
      connP (oddEdges (withGhost G).edgeFinset fib) (some o) a →
      hnw_mass (withGhost G) β J' fib {some o, a} = hnw_mass (withGhost G) β J' fib ∅ := by
    intro a hoa Harc
    have := hnw_switching (withGhost G) β J' fib hoa Harc ∅
    rwa [show (∅ : Finset (Option V)) ∆ {some o, a} = {some o, a} from by simp] at this
  have htri := gc21_fibre_posTrichotomy G m K₁ (some o) (some x) (some y) none
    hoxs hoys hog hxys hxgs hygs hbdry
  rcases htri with hOg | hp1 | hp2
  · rw [collapse none hog (hbridge K₁ (some o) none hOg)]; linarith
  · rw [collapse (some x) hoxs (hbridge K₁ (some o) (some x) hp1.1)]; linarith
  · rw [collapse (some y) hoys (hbridge K₁ (some o) (some y) hp2.1)]; linarith


theorem gc21_firstFour_nonpos_of_bridge (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (m : ↥(withGhost G).edgeFinset → ℕ) (hbridge : gc21_FibreOddArcBridge G m)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hbdry : sources (withGhost G) (ofEdgeFun (withGhost G) m)
        = ({some o, some x, some y, none} : Finset (Option V))) :
    gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ ∅
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, none}
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some x}
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some y} ≤ 0 := by
  have hJnn : ∀ e, (0 : ℝ) ≤ ghostCoupling h β (fun _ => 1) e :=
    gc6_ghostCoupling_nonneg (V := V) β h hh
  rw [gc18_firstFour_reorg G β h o x y m]
  refine Finset.sum_nonpos (fun K₂ _ => ?_)
  by_cases hK₂ : sources (withGhost G) (ofEdgeFun (withGhost G) K₂.1) = ∅
  · rw [if_pos hK₂]
    have hw : (0 : ℝ) ≤ weight (withGhost G) β (ghostCoupling h β (fun _ => 1))
        (ofEdgeFun (withGhost G) K₂.1) :=
      asd_weight_nonneg (withGhost G) β (ghostCoupling h β (fun _ => 1)) hβ hJnn _
    
    have hinner : sources (withGhost G) (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))
        = ({some o, some x, some y, none} : Finset (Option V)) := by
      have hadd := sources_ofEdgeFun_add (withGhost G) m K₂.1 K₂.2
      rw [hbdry, hK₂] at hadd
      rw [show (∅ : Finset (Option V)) ∆
            sources (withGhost G) (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))
          = sources (withGhost G) (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))
          from symmDiff_eq_right.mpr rfl] at hadd
      exact hadd.symm
    have hsg := gc21_fibre_starGap_nonpos_of_bridge G β h hβ hh o x y m hbridge K₂
      hox hoy hxy hinner
    exact mul_nonpos_of_nonneg_of_nonpos hw hsg
  · rw [if_neg hK₂, zero_mul]

end StatMech.Walls
