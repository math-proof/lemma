/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.SuperMultiplicative.Part4
import Theorem.StatisticalMechanics.Code.FK.FKInterfaceSubadd.Part2
import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
import Theorem.StatisticalMechanics.Code.FK.CenteredFreeEnergy.Part3
import Theorem.StatisticalMechanics.Code.FK.BoxFeketePerVolume.Part2
import Def.StatisticalMechanics.Code.FK.EdgeConfigZ.Part14
open scoped BigOperators
open SimpleGraph Filter Topology Set

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000


namespace StatMech

namespace FK

open StatMech.Lattice


section BoxNesting

variable {d : ℕ}


section VanHove

variable {d : ℕ}


theorem ecz_perEdge_vanHove (m n : ℕ) (s : ℝ)
    (hEn : 0 < (boxGraph d n).edgeFinset.card) (hEm : 0 < (boxGraph d m).edgeFinset.card) :
    ecz_f d s n
      ≤ (((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ)
            / ((boxGraph d n).edgeFinset.card : ℝ)) * ecz_f d s m
        + (1 - ((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ)
            / ((boxGraph d n).edgeFinset.card : ℝ)) * (-Real.log (1 - fsc_logistic s)) := by
  set c := -Real.log (1 - fsc_logistic s) with hc
  have hEnR : (0 : ℝ) < ((boxGraph d n).edgeFinset.card : ℝ) := by exact_mod_cast hEn
  have hEmR : (0 : ℝ) < ((boxGraph d m).edgeFinset.card : ℝ) := by exact_mod_cast hEm
  have hsub := ecz_box_vanHove_subadd (d := d) m n s
  rw [← hc] at hsub
  
  rw [ecz_f, ecz_f]
  set En : ℝ := ((boxGraph d n).edgeFinset.card : ℝ) with hEnDef
  set Em : ℝ := ((boxGraph d m).edgeFinset.card : ℝ) with hEmDef
  set Td : ℝ := ((ecz_T m n) ^ d : ℝ) with hTd
  rw [div_le_iff₀ hEnR]
  
  have hEmne : Em ≠ 0 := ne_of_gt hEmR
  have hkey : (Td * Em / En * (ecz_u d s m / Em) + (1 - Td * Em / En) * c) * En
      = Td * ecz_u d s m + (En - Td * Em) * c := by
    field_simp
  calc ecz_u d s n ≤ Td * ecz_u d s m + (En - Td * Em) * c := hsub
    _ = (Td * Em / En * (ecz_u d s m / Em) + (1 - Td * Em / En) * c) * En := hkey.symm


theorem ecz_dyadic_f_tendsto (hd : 1 ≤ d) (s : ℝ)
    (hbox : ∀ j, 0 < (boxGraph d (agl_K j)).edgeFinset.card) :
    ∃ L : ℝ, Tendsto (fun j => ecz_f d s (agl_K j)) atTop (𝓝 L) := by
  classical
  obtain ⟨I, hInn, hIsum, hudbl, hEdge⟩ := ecz_additiveDoublingBound d hd s
  set c : ℝ := -Real.log (1 - fsc_logistic s) with hc
  have hp1 : fsc_logistic s < 1 := fsc_logistic_lt_one s
  have hp0 : (0:ℝ) < fsc_logistic s := fsc_logistic_pos s
  have hc0 : 0 ≤ c := by rw [hc, neg_nonneg]; exact Real.log_nonpos (by linarith) (by linarith)
  have hEpos : ∀ j, 0 < agl_E d (agl_K j) := fun j => by
    unfold agl_E; exact_mod_cast hbox j
  set M : ℝ := 3 * Real.log 2 + c with hM
  have hMc0 : 0 ≤ M + c := by
    rw [hM]; have hl2 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num); linarith
  have hIE0 : ∀ j, 0 ≤ I j / agl_E d (agl_K (j + 1)) := fun j =>
    div_nonneg (hInn j) (hEpos (j + 1)).le
  set δ : ℕ → ℝ := fun j => (M + c) * (I j / agl_E d (agl_K (j + 1))) with hδ
  
  have hmono : ∀ j, ecz_edgeFreeEnergy d s (agl_K j) - δ j ≤ ecz_edgeFreeEnergy d s (agl_K (j + 1)) := by
    intro j
    rw [ecz_edgeFE_eq s (agl_K j), ecz_edgeFE_eq s (agl_K (j + 1))]
    have hstep := bxt_perVolume_doubling_step (a := ecz_u d s (agl_K j))
      (A := ecz_u d s (agl_K (j + 1))) (e := agl_E d (agl_K j)) (E := agl_E d (agl_K (j + 1)))
      (K := (2 : ℝ) ^ d) (c := c) (i := I j)
      (hEpos j) (hEpos (j + 1)) hc0 (hInn j) (hudbl j) (hEdge j)
    have hl2 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hupper : -(ecz_u d s (agl_K j) / agl_E d (agl_K j)) ≤ 3 * Real.log 2 := by
      have h := ecz_edgeFE_le_const d (agl_K j) hd (agl_K_pos j) s (hbox j)
      rw [ecz_edgeFE_eq] at h; linarith
    have hlower : ecz_u d s (agl_K j) / agl_E d (agl_K j) ≤ c := by
      have hEr : (0:ℝ) < agl_E d (agl_K j) := hEpos j
      have hge := ecz_neglogZEdge_le_edges (boxGraph d (agl_K j)) hp0 hp1 (by norm_num : (1:ℝ) ≤ 2)
      rw [div_le_iff₀ hEr]
      show ecz_u d s (agl_K j) ≤ c * agl_E d (agl_K j)
      have : ecz_u d s (agl_K j) ≤ agl_E d (agl_K j) * c := by
        simpa [ecz_u, agl_E, hc] using hge
      linarith [mul_comm (agl_E d (agl_K j)) c, this]
    have huEbd : |ecz_u d s (agl_K j)| / agl_E d (agl_K j) ≤ M := by
      have hquot : |ecz_u d s (agl_K j)| / agl_E d (agl_K j)
          = |ecz_u d s (agl_K j) / agl_E d (agl_K j)| := by
        rw [abs_div, abs_of_pos (hEpos j)]
      rw [hquot, abs_le]
      exact ⟨by rw [hM]; linarith [hupper, hc0], by rw [hM]; linarith [hlower, hl2]⟩
    have hdefle : (|ecz_u d s (agl_K j)| / agl_E d (agl_K j) + c)
        * (I j / agl_E d (agl_K (j + 1))) ≤ δ j := by
      show _ ≤ (M + c) * (I j / agl_E d (agl_K (j + 1)))
      apply mul_le_mul_of_nonneg_right _ (hIE0 j)
      linarith [huEbd]
    have hgoal : -(ecz_u d s (agl_K j) / agl_E d (agl_K j)) - δ j
        ≤ -(ecz_u d s (agl_K (j + 1)) / agl_E d (agl_K (j + 1))) := by linarith [hstep, hdefle]
    linarith
  
  have hbdd : BddAbove (Set.range fun j => ecz_edgeFreeEnergy d s (agl_K j)) := by
    refine ⟨3 * Real.log 2 + Real.log (1 + Real.exp s), ?_⟩
    rintro x ⟨j, rfl⟩
    simp only
    exact ecz_edgeFE_le_const d (agl_K j) hd (agl_K_pos j) s (hbox j)
  
  obtain ⟨L', hL'⟩ := agl_subseq_almost_mono_converges
    (fun n => ecz_edgeFreeEnergy d s n) agl_K δ
    (fun j => mul_nonneg hMc0 (hIE0 j)) (hIsum.mul_left (M + c)) hmono hbdd
  refine ⟨Real.log (1 + Real.exp s) - L', ?_⟩
  have heq : ∀ j, ecz_f d s (agl_K j)
      = Real.log (1 + Real.exp s) - ecz_edgeFreeEnergy d s (agl_K j) := by
    intro j; rw [ecz_f, ecz_edgeFE_eq, agl_E]; ring
  rw [show (fun j => ecz_f d s (agl_K j))
      = (fun j => Real.log (1 + Real.exp s) - ecz_edgeFreeEnergy d s (agl_K j)) from
    funext heq]
  have := (hL'.const_sub (Real.log (1 + Real.exp s)))
  simpa using this


theorem ecz_f_bounds (hd : 1 ≤ d) (s : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hEn : 0 < (boxGraph d n).edgeFinset.card) :
    -(3 * Real.log 2) ≤ ecz_f d s n ∧ ecz_f d s n ≤ -Real.log (1 - fsc_logistic s) := by
  set c := -Real.log (1 - fsc_logistic s) with hc
  have hp0 : (0:ℝ) < fsc_logistic s := fsc_logistic_pos s
  have hp1 : fsc_logistic s < 1 := fsc_logistic_lt_one s
  have hEnR : (0 : ℝ) < ((boxGraph d n).edgeFinset.card : ℝ) := by exact_mod_cast hEn
  refine ⟨?_, ?_⟩
  · 
    have h := ecz_edgeFE_le_const d n hd hn s hEn
    rw [ecz_edgeFE_eq, agl_E] at h
    rw [ecz_f]
    have hlog1 : (0:ℝ) ≤ Real.log (1 + Real.exp s) :=
      Real.log_nonneg (by have := Real.exp_pos s; linarith)
    linarith
  · 
    have hge := ecz_neglogZEdge_le_edges (boxGraph d n) hp0 hp1 (by norm_num : (1:ℝ) ≤ 2)
    rw [ecz_f, div_le_iff₀ hEnR]
    have : ecz_u d s n ≤ ((boxGraph d n).edgeFinset.card : ℝ) * c := by
      simpa [ecz_u, hc] using hge
    linarith [this, mul_comm ((boxGraph d n).edgeFinset.card : ℝ) c]


theorem ecz_f_lower (hd : 1 ≤ d) (s : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hbox : ∀ k, 1 ≤ k → 0 < (boxGraph d k).edgeFinset.card) (L : ℝ)
    (hL : Tendsto (fun j => ecz_f d s (agl_K j)) atTop (𝓝 L)) :
    ((2 * (n : ℝ) + 1) / (2 * n)) * L - (-Real.log (1 - fsc_logistic s)) / (2 * n)
      ≤ ecz_f d s n := by
  set c := -Real.log (1 - fsc_logistic s) with hc
  have hp0 : (0:ℝ) < fsc_logistic s := fsc_logistic_pos s
  have hp1 : fsc_logistic s < 1 := fsc_logistic_lt_one s
  have hc0 : 0 ≤ c := by rw [hc, neg_nonneg]; exact Real.log_nonpos (by linarith) (by linarith)
  have hEnR : (0 : ℝ) < ((boxGraph d n).edgeFinset.card : ℝ) := by exact_mod_cast hbox n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h2n : (0 : ℝ) < 2 * n := by positivity
  
  
  set rfun : ℕ → ℝ := fun j => ((ecz_T n (agl_K j)) ^ d : ℝ)
    * ((boxGraph d n).edgeFinset.card : ℝ) / ((boxGraph d (agl_K j)).edgeFinset.card : ℝ) with hrfun
  have hr_tendsto : Tendsto rfun atTop (𝓝 (2 * (n : ℝ) / (2 * n + 1))) :=
    ecz_bulkFraction_tendsto hd n hn |>.comp agl_K_tendsto_atTop
  
  
  have hr_pos : ∀ j, 0 < ((boxGraph d (agl_K j)).edgeFinset.card : ℝ) := fun j => by
    exact_mod_cast hbox (agl_K j) (agl_K_pos j)
  
  
  have hbound : ∀ j, n ≤ agl_K j →
      ecz_f d s (agl_K j) ≤ rfun j * ecz_f d s n + (1 - rfun j) * c := by
    intro j hj
    have := ecz_perEdge_vanHove (d := d) n (agl_K j) s (hbox (agl_K j) (agl_K_pos j)) (hbox n hn)
    rw [← hc] at this
    simpa [hrfun] using this
  
  have hrinf_pos : (0 : ℝ) < 2 * (n : ℝ) / (2 * n + 1) := by positivity
  
  have hRHS_tendsto : Tendsto (fun j => rfun j * ecz_f d s n + (1 - rfun j) * c) atTop
      (𝓝 ((2 * (n : ℝ) / (2 * n + 1)) * ecz_f d s n
          + (1 - 2 * (n : ℝ) / (2 * n + 1)) * c)) :=
    ((hr_tendsto.mul tendsto_const_nhds).add
      (((tendsto_const_nhds).sub hr_tendsto).mul tendsto_const_nhds))
  
  have hKge : ∀ᶠ j in atTop, n ≤ agl_K j := by
    have := agl_K_tendsto_atTop.eventually_ge_atTop n
    exact this
  have hLle : L ≤ (2 * (n : ℝ) / (2 * n + 1)) * ecz_f d s n + (1 - 2 * (n : ℝ) / (2 * n + 1)) * c := by
    refine le_of_tendsto_of_tendsto hL hRHS_tendsto ?_
    filter_upwards [hKge] with j hj using hbound j hj
  
  set R : ℝ := 2 * (n : ℝ) / (2 * n + 1) with hR
  have hRpos : 0 < R := hrinf_pos
  
  have h2n1 : (0:ℝ) < 2 * (n:ℝ) + 1 := by positivity
  
  have hfn : (L - (1 - R) * c) / R ≤ ecz_f d s n := by
    rw [div_le_iff₀ hRpos]; nlinarith [hLle]
  have hsimp : (L - (1 - R) * c) / R
      = (2 * (n : ℝ) + 1) / (2 * n) * L - c / (2 * n) := by
    rw [hR]; field_simp; ring
  rw [hsimp] at hfn
  linarith [hfn]


end VanHove
end BoxNesting
end FK
end StatMech
