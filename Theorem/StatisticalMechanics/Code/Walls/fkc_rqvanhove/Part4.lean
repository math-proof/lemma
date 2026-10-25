/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fkc_rqvanhove.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.fkc_rqbdd.Part2
import Theorem.StatisticalMechanics.Code.Walls.fkc_rqbulkfraction
import Def.StatisticalMechanics.Code.Walls.fkc_rqvanhove.Part4
open scoped BigOperators
open SimpleGraph Filter Topology Set

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 2000000


namespace StatMech.Walls

open StatMech StatMech.FK StatMech.Lattice


theorem fkc_g_dyadic_tendsto (d : ℕ) (s q L : ℝ)
    (hL : Tendsto (fun j => fkc_f d s q (agl_K j)) atTop (nhds L)) :
    Tendsto (fun j => fkc_g d s q (agl_K j)) atTop (nhds L) := by
  set c := -Real.log (1 - fsc_logistic s) with hc
  have hKtop : Tendsto (fun j => (2 * ((agl_K j : ℕ) : ℝ) + 1)) atTop atTop :=
    ecz_denom_tendsto_atTop.comp (by exact_mod_cast agl_K_tendsto_atTop)
  have h0 : Tendsto (fun j => (1 : ℝ) / (2 * ((agl_K j : ℕ) : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hKtop
  have hR : Tendsto (fun j => 2 * ((agl_K j : ℕ) : ℝ)
      / (2 * ((agl_K j : ℕ) : ℝ) + 1)) atTop (nhds 1) := by
    have heq : ∀ j, 2 * ((agl_K j : ℕ) : ℝ) / (2 * ((agl_K j : ℕ) : ℝ) + 1)
        = 1 - 1 / (2 * ((agl_K j : ℕ) : ℝ) + 1) := by
      intro j; field_simp; ring
    rw [show (fun j => 2 * ((agl_K j : ℕ) : ℝ) / (2 * ((agl_K j : ℕ) : ℝ) + 1))
        = fun j => 1 - 1 / (2 * ((agl_K j : ℕ) : ℝ) + 1) from funext heq]
    simpa using h0.const_sub (1 : ℝ)
  have hprod : Tendsto (fun j =>
      (2 * ((agl_K j : ℕ) : ℝ) / (2 * ((agl_K j : ℕ) : ℝ) + 1))
          * fkc_f d s q (agl_K j)
        + (1 - 2 * ((agl_K j : ℕ) : ℝ) / (2 * ((agl_K j : ℕ) : ℝ) + 1)) * c)
      atTop (nhds ((1 : ℝ) * L + (1 - 1) * c)) :=
    (hR.mul hL).add (((tendsto_const_nhds (x := (1 : ℝ))).sub hR).mul
      (tendsto_const_nhds (x := c)))
  have heq : (fun j => fkc_g d s q (agl_K j))
      = fun j => (2 * ((agl_K j : ℕ) : ℝ) / (2 * ((agl_K j : ℕ) : ℝ) + 1))
          * fkc_f d s q (agl_K j)
        + (1 - 2 * ((agl_K j : ℕ) : ℝ) / (2 * ((agl_K j : ℕ) : ℝ) + 1)) * c := by
    funext j; rw [fkc_g, hc]
  rw [heq]
  simpa using hprod


theorem fkc_upperSeq_tendsto (d : ℕ) (hd : 1 ≤ d) (s q : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    Tendsto (fun n =>
        (((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ)
            / ((boxGraph d n).edgeFinset.card : ℝ)) * fkc_f d s q m
        + (1 - ((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ)
            / ((boxGraph d n).edgeFinset.card : ℝ)) * (-Real.log (1 - fsc_logistic s))) atTop
      (nhds (fkc_g d s q m)) := by
  have hr := ecz_bulkFraction_tendsto (d := d) hd m hm
  rw [fkc_g]
  exact (hr.mul tendsto_const_nhds).add ((tendsto_const_nhds.sub hr).mul tendsto_const_nhds)


theorem fkc_perEdgeDensityConverges (d : ℕ) (hd : 1 ≤ d) (s q : ℝ) (hq : 1 ≤ q) :
    fkc_PerEdgeDensityConverges d s q := by
  classical
  obtain ⟨L, hL⟩ := fkc_dyadic_f_tendsto d hd s q hq
  set c := -Real.log (1 - fsc_logistic s) with hc
  refine ⟨L, ?_⟩
  have hgK := fkc_g_dyadic_tendsto d s q L hL
  have hlower : Tendsto
      (fun n : ℕ => ((2 * (n : ℝ) + 1) / (2 * n)) * L - c / (2 * n)) atTop (nhds L) := by
    have h1 := ecz_oddEven_ratio_tendsto.mul (tendsto_const_nhds (x := L))
    have hden : Tendsto (fun n : ℕ => (2 * (n : ℝ))) atTop atTop :=
      Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun n : ℕ => c / (2 * (n : ℝ))) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop hden
    simpa using h1.sub h2
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N1, hN1⟩ := (Metric.tendsto_atTop.mp hlower) (ε / 2) (by linarith)
  obtain ⟨J, hJ⟩ := (Metric.tendsto_atTop.mp hgK) (ε / 2) (by linarith)
  have hgJ : fkc_g d s q (agl_K J) < L + ε / 2 := by
    have h := hJ J (le_refl _)
    rw [Real.dist_eq, abs_lt] at h
    linarith
  have hu := fkc_upperSeq_tendsto d hd s q (agl_K J) (agl_K_pos J)
  obtain ⟨N2, hN2⟩ := (Metric.tendsto_atTop.mp hu) (ε / 2) (by linarith)
  refine ⟨max (max N1 N2) 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnN1 : N1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnN2 : N2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  rw [Real.dist_eq, abs_lt]
  constructor
  · have hle := fkc_f_lower d hd s q hq n hn1 L hL
    rw [← hc] at hle
    have hclose := hN1 n hnN1
    rw [Real.dist_eq, abs_lt] at hclose
    linarith
  · have hle := fkc_perEdge_vanHove d (agl_K J) n s q hq
      (ecz_box_edge_pos d hd hn1) (ecz_box_edge_pos d hd (agl_K_pos J))
    have hclose := hN2 n hnN2
    rw [Real.dist_eq, abs_lt] at hclose
    linarith

end StatMech.Walls
