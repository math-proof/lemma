/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.EdgeConfigZ.Part15
import Theorem.StatisticalMechanics.Code.Walls.fc_weightle
import Theorem.StatisticalMechanics.Code.Walls.fc_allclosed
import Theorem.StatisticalMechanics.Code.Walls.fc_bulkfraction
import Def.StatisticalMechanics.Code.Walls.fc_core.Part5
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

namespace Walls

open StatMech.FK StatMech.Lattice


variable {d : ℕ}


theorem fc_additiveDoublingBound (d : ℕ) (hd : 1 ≤ d) {q : ℝ} (hq : 1 ≤ q) (t : ℝ) :
    fc_AdditiveDoublingBound d q t := by
  set c := -Real.log (1 - fsc_logistic t) with hc
  have hp0 : (0 : ℝ) < fsc_logistic t := fsc_logistic_pos t
  have hp1 : fsc_logistic t < 1 := fsc_logistic_lt_one t
  have hc0 : 0 ≤ c := by rw [hc, neg_nonneg]; exact Real.log_nonpos (by linarith) (by linarith)
  set N : ℕ → ℝ := fun j => ((2 * d * (qp_Jset d (agl_K j)).card
    + (2 ^ d + 1) * (2 * d * (qp_Jset d (agl_K j)).card) : ℕ) : ℝ) with hN
  set G : ℕ → ℝ := fun j => agl_E d (agl_K (j + 1)) - (2 : ℝ) ^ d * agl_E d (agl_K j) with hG
  have hKsucc : ∀ j, agl_K (j + 1) = 2 * agl_K j + 1 := agl_K_succ
  have hGnn : ∀ j, 0 ≤ G j := by
    intro j; rw [hG]; simp only
    have h := qp_edge_le d (agl_K j) hd
    rw [show agl_E d (agl_K (j + 1)) = agl_E d (2 * agl_K j + 1) from by rw [agl_K_succ]]
    rw [agl_E, agl_E]; linarith [h]
  set I : ℕ → ℝ := fun j => N j + G j with hI
  have hInn : ∀ j, 0 ≤ I j := by
    intro j; rw [hI]; have : 0 ≤ N j := Nat.cast_nonneg _; linarith [hGnn j]
  refine ⟨I, hInn, ?_, ?_, ?_⟩
  · apply qp_summable_ratio d hd I _ hInn
    intro j
    have hNb : N j ≤ ((2 ^ d + 2) * (2 * d * d) : ℝ) * (4 * (agl_K j : ℝ) + 3) ^ (d - 1) := by
      simp only [hN]
      have hJ : (qp_Jset d (agl_K j)).card ≤ d * (2 * (2 * agl_K j + 1) + 1) ^ (d - 1) :=
        qp_Jset_card_le d (agl_K j) hd
      rw [show (2 * d * (qp_Jset d (agl_K j)).card + (2 ^ d + 1) * (2 * d * (qp_Jset d (agl_K j)).card))
            = (2 ^ d + 2) * (2 * d * (qp_Jset d (agl_K j)).card) from by ring]
      push_cast
      have hbase : (2 * (2 * (agl_K j : ℝ) + 1) + 1) = 4 * (agl_K j : ℝ) + 3 := by ring
      have hJR : ((qp_Jset d (agl_K j)).card : ℝ)
          ≤ (d : ℝ) * (4 * (agl_K j : ℝ) + 3) ^ (d - 1) := by
        calc ((qp_Jset d (agl_K j)).card : ℝ)
            ≤ ((d * (2 * (2 * agl_K j + 1) + 1) ^ (d - 1) : ℕ) : ℝ) := by exact_mod_cast hJ
          _ = (d : ℝ) * (2 * (2 * (agl_K j : ℝ) + 1) + 1) ^ (d - 1) := by push_cast; ring
          _ = (d : ℝ) * (4 * (agl_K j : ℝ) + 3) ^ (d - 1) := by rw [hbase]
      calc ((2 : ℝ) ^ d + 2) * (2 * d * ((qp_Jset d (agl_K j)).card : ℝ))
          ≤ ((2 : ℝ) ^ d + 2) * (2 * d * ((d : ℝ) * (4 * (agl_K j : ℝ) + 3) ^ (d - 1))) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply mul_le_mul_of_nonneg_left hJR (by positivity)
        _ = ((2 : ℝ) ^ d + 2) * (2 * d * d) * (4 * (agl_K j : ℝ) + 3) ^ (d - 1) := by ring
    have hGb : G j ≤ ((d : ℝ) * (d + 2)) * (4 * (agl_K j : ℝ) + 3) ^ (d - 1) := by
      rw [hG]; simp only
      rw [show agl_E d (agl_K (j + 1)) = agl_E d (2 * agl_K j + 1) from by rw [agl_K_succ]]
      have h := qp_edge_gap_le d (agl_K j) hd
      rw [agl_E, agl_E]; linarith [h]
    rw [hI]; linarith [hNb, hGb]
  · intro j
    have hdbl := fc_box_neglog_doubling d (agl_K j) hq t
    rw [show fc_u d q t (agl_K (j + 1)) = fc_u d q t (2 * agl_K j + 1) from by rw [agl_K_succ]]
    have hge : N j * c ≤ I j * c := by
      rw [hI]; apply mul_le_mul_of_nonneg_right _ hc0; linarith [hGnn j]
    calc fc_u d q t (2 * agl_K j + 1)
        ≤ (2 : ℝ) ^ d * fc_u d q t (agl_K j) + N j * c := hdbl
      _ ≤ (2 : ℝ) ^ d * fc_u d q t (agl_K j) + I j * c := by linarith
  · intro j
    have hGval : G j = agl_E d (agl_K (j + 1)) - (2 : ℝ) ^ d * agl_E d (agl_K j) := rfl
    rw [abs_of_nonpos (by have := hGnn j; rw [hGval] at this; linarith)]
    rw [hI]; have hNn : 0 ≤ N j := Nat.cast_nonneg _
    have hGeq : -((2 : ℝ) ^ d * agl_E d (agl_K j) - agl_E d (agl_K (j + 1))) = G j := by
      rw [hGval]; ring
    rw [hGeq]; linarith


theorem fc_box_vanHove_subadd (m n : ℕ) {q : ℝ} (hq : 1 ≤ q) (t : ℝ) :
    fc_u d q t n ≤ ((ecz_T m n) ^ d : ℝ) * fc_u d q t m
      + (((boxGraph d n).edgeFinset.card : ℝ)
          - ((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ))
          * (-Real.log (1 - fsc_logistic t)) := by
  classical
  set p := fsc_logistic t with hp
  have hp0 : (0 : ℝ) < p := fsc_logistic_pos t
  have hp1 : p < 1 := fsc_logistic_lt_one t
  have hq0 : (0:ℝ) < q := by linarith
  set c := -Real.log (1 - p) with hc
  have hc0 : 0 ≤ c := by rw [hc, neg_nonneg]; exact Real.log_nonpos (by linarith) (by linarith)
  set tag := ecz_vanHoveTag m n with htag
  set K₀ := boxGraph d n with hK₀
  have hsub := ecz_multiblock_subadd K₀ tag p q hp0 hp1 hq0 Finset.univ
  have hrest_u : ecz_uu (qp_restG K₀ tag Finset.univ) p q = fc_u d q t n := by
    rw [ecz_uu, fc_u, hp, ecz_fkZEdge_iso (ecz_restUnivIso m n) p q]
  have hrest_E : ((qp_restG K₀ tag Finset.univ).edgeFinset.card : ℝ)
      = ((boxGraph d n).edgeFinset.card : ℝ) := by
    rw [(ecz_restUnivIso m n).card_edgeFinset_eq]
  have hsplit_u : (∑ τ : Option (Fin d → Fin (ecz_T m n)), ecz_uu (qp_blkG K₀ tag τ) p q)
      = ecz_uu (qp_blkG K₀ tag none) p q
        + ((ecz_T m n) ^ d : ℝ) * fc_u d q t m := by
    rw [Fintype.sum_option]
    congr 1
    have heach : ∀ cc : Fin d → Fin (ecz_T m n),
        ecz_uu (qp_blkG K₀ tag (some cc)) p q = fc_u d q t m := fun cc => by
      rw [ecz_uu, fc_u, hp, ecz_cellBlock_fkZEdge m n cc]
    rw [Finset.sum_congr rfl (fun cc _ => heach cc), Finset.sum_const, Finset.card_univ,
      ecz_cell_card, nsmul_eq_mul]
    push_cast; ring
  have hsplit_E : (∑ τ : Option (Fin d → Fin (ecz_T m n)),
        ((qp_blkG K₀ tag τ).edgeFinset.card : ℝ))
      = ((qp_blkG K₀ tag none).edgeFinset.card : ℝ)
        + ((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ) := by
    rw [Fintype.sum_option]
    congr 1
    have heach : ∀ cc : Fin d → Fin (ecz_T m n),
        ((qp_blkG K₀ tag (some cc)).edgeFinset.card : ℝ) = ((boxGraph d m).edgeFinset.card : ℝ) :=
      fun cc => by rw [ecz_cellBlock_edge_card m n cc]
    rw [Finset.sum_congr rfl (fun cc _ => heach cc), Finset.sum_const, Finset.card_univ,
      ecz_cell_card, nsmul_eq_mul]
    push_cast; ring
  have hnone : ecz_uu (qp_blkG K₀ tag none) p q
      ≤ ((qp_blkG K₀ tag none).edgeFinset.card : ℝ) * c := by
    rw [ecz_uu, hc]; exact ecz_neglogZEdge_le_edges _ hp0 hp1 hq
  rw [show (∑ τ ∈ (Finset.univ : Finset (Option (Fin d → Fin (ecz_T m n)))),
        ecz_uu (qp_blkG K₀ tag τ) p q)
      = ∑ τ : Option (Fin d → Fin (ecz_T m n)), ecz_uu (qp_blkG K₀ tag τ) p q from rfl] at hsub
  rw [show (∑ τ ∈ (Finset.univ : Finset (Option (Fin d → Fin (ecz_T m n)))),
        ((qp_blkG K₀ tag τ).edgeFinset.card : ℝ))
      = ∑ τ : Option (Fin d → Fin (ecz_T m n)), ((qp_blkG K₀ tag τ).edgeFinset.card : ℝ) from rfl]
    at hsub
  rw [hrest_u, hsplit_u, hrest_E, hsplit_E] at hsub
  set uNone : ℝ := ecz_uu (qp_blkG K₀ tag none) p q with huNone
  set ENone : ℝ := ((qp_blkG K₀ tag none).edgeFinset.card : ℝ) with hENone
  set Td : ℝ := ((ecz_T m n) ^ d : ℝ) with hTd
  set Um : ℝ := fc_u d q t m with hUm
  set Em : ℝ := ((boxGraph d m).edgeFinset.card : ℝ) with hEm
  set En : ℝ := ((boxGraph d n).edgeFinset.card : ℝ) with hEn
  have hexpand : (En - (ENone + Td * Em)) * c = (En - Td * Em) * c - ENone * c := by ring
  rw [hexpand] at hsub
  linarith [hsub, hnone]


theorem fc_perEdge_vanHove (m n : ℕ) {q : ℝ} (hq : 1 ≤ q) (s : ℝ)
    (hEn : 0 < (boxGraph d n).edgeFinset.card) (hEm : 0 < (boxGraph d m).edgeFinset.card) :
    fc_f d q s n
      ≤ (((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ)
            / ((boxGraph d n).edgeFinset.card : ℝ)) * fc_f d q s m
        + (1 - ((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ)
            / ((boxGraph d n).edgeFinset.card : ℝ)) * (-Real.log (1 - fsc_logistic s)) := by
  set c := -Real.log (1 - fsc_logistic s) with hc
  have hEnR : (0 : ℝ) < ((boxGraph d n).edgeFinset.card : ℝ) := by exact_mod_cast hEn
  have hEmR : (0 : ℝ) < ((boxGraph d m).edgeFinset.card : ℝ) := by exact_mod_cast hEm
  have hsub := fc_box_vanHove_subadd (d := d) m n hq s
  rw [← hc] at hsub
  rw [fc_f, fc_f]
  set En : ℝ := ((boxGraph d n).edgeFinset.card : ℝ) with hEnDef
  set Em : ℝ := ((boxGraph d m).edgeFinset.card : ℝ) with hEmDef
  set Td : ℝ := ((ecz_T m n) ^ d : ℝ) with hTd
  rw [div_le_iff₀ hEnR]
  have hEmne : Em ≠ 0 := ne_of_gt hEmR
  have hkey : (Td * Em / En * (fc_u d q s m / Em) + (1 - Td * Em / En) * c) * En
      = Td * fc_u d q s m + (En - Td * Em) * c := by
    field_simp
  calc fc_u d q s n ≤ Td * fc_u d q s m + (En - Td * Em) * c := hsub
    _ = (Td * Em / En * (fc_u d q s m / Em) + (1 - Td * Em / En) * c) * En := hkey.symm


theorem fc_dyadic_f_tendsto (hd : 1 ≤ d) {q : ℝ} (hq : 1 ≤ q) (s : ℝ)
    (hbox : ∀ j, 0 < (boxGraph d (agl_K j)).edgeFinset.card) :
    ∃ L : ℝ, Tendsto (fun j => fc_f d q s (agl_K j)) atTop (𝓝 L) := by
  classical
  obtain ⟨I, hInn, hIsum, hudbl, hEdge⟩ := fc_additiveDoublingBound d hd hq s
  set c : ℝ := -Real.log (1 - fsc_logistic s) with hc
  have hp1 : fsc_logistic s < 1 := fsc_logistic_lt_one s
  have hp0 : (0:ℝ) < fsc_logistic s := fsc_logistic_pos s
  have hc0 : 0 ≤ c := by rw [hc, neg_nonneg]; exact Real.log_nonpos (by linarith) (by linarith)
  have hEpos : ∀ j, 0 < agl_E d (agl_K j) := fun j => by
    unfold agl_E; exact_mod_cast hbox j
  set M : ℝ := fc_C q + c with hM
  have hMc0 : 0 ≤ M + c := by
    rw [hM]; have := fc_C_nonneg hq; linarith
  have hIE0 : ∀ j, 0 ≤ I j / agl_E d (agl_K (j + 1)) := fun j =>
    div_nonneg (hInn j) (hEpos (j + 1)).le
  set δ : ℕ → ℝ := fun j => (M + c) * (I j / agl_E d (agl_K (j + 1))) with hδ
  have hmono : ∀ j, fc_edgeFreeEnergy d q s (agl_K j) - δ j ≤ fc_edgeFreeEnergy d q s (agl_K (j + 1)) := by
    intro j
    rw [fc_edgeFE_eq q s (agl_K j), fc_edgeFE_eq q s (agl_K (j + 1))]
    have hstep := bxt_perVolume_doubling_step (a := fc_u d q s (agl_K j))
      (A := fc_u d q s (agl_K (j + 1))) (e := agl_E d (agl_K j)) (E := agl_E d (agl_K (j + 1)))
      (K := (2 : ℝ) ^ d) (c := c) (i := I j)
      (hEpos j) (hEpos (j + 1)) hc0 (hInn j) (hudbl j) (hEdge j)
    have hupper : -(fc_u d q s (agl_K j) / agl_E d (agl_K j)) ≤ fc_C q := by
      have h := fc_edgeFE_le_const d (agl_K j) hd (agl_K_pos j) hq s (hbox j)
      rw [fc_edgeFE_eq] at h
      have hlog1 : (0:ℝ) ≤ Real.log (1 + Real.exp s) :=
        Real.log_nonneg (by have := Real.exp_pos s; linarith)
      linarith
    have hlower : fc_u d q s (agl_K j) / agl_E d (agl_K j) ≤ c := by
      have hEr : (0:ℝ) < agl_E d (agl_K j) := hEpos j
      have hge := fc_u_le_edges (d := d) q hq s (agl_K j)
      rw [div_le_iff₀ hEr]
      show fc_u d q s (agl_K j) ≤ c * agl_E d (agl_K j)
      have : fc_u d q s (agl_K j) ≤ agl_E d (agl_K j) * c := by
        simpa [agl_E, hc] using hge
      linarith [mul_comm (agl_E d (agl_K j)) c, this]
    have huEbd : |fc_u d q s (agl_K j)| / agl_E d (agl_K j) ≤ M := by
      have hquot : |fc_u d q s (agl_K j)| / agl_E d (agl_K j)
          = |fc_u d q s (agl_K j) / agl_E d (agl_K j)| := by
        rw [abs_div, abs_of_pos (hEpos j)]
      rw [hquot, abs_le]
      exact ⟨by rw [hM]; linarith [hupper, hc0], by rw [hM]; linarith [hlower, fc_C_nonneg hq]⟩
    have hdefle : (|fc_u d q s (agl_K j)| / agl_E d (agl_K j) + c)
        * (I j / agl_E d (agl_K (j + 1))) ≤ δ j := by
      show _ ≤ (M + c) * (I j / agl_E d (agl_K (j + 1)))
      apply mul_le_mul_of_nonneg_right _ (hIE0 j)
      linarith [huEbd]
    have hgoal : -(fc_u d q s (agl_K j) / agl_E d (agl_K j)) - δ j
        ≤ -(fc_u d q s (agl_K (j + 1)) / agl_E d (agl_K (j + 1))) := by linarith [hstep, hdefle]
    linarith
  have hbdd : BddAbove (Set.range fun j => fc_edgeFreeEnergy d q s (agl_K j)) := by
    refine ⟨fc_C q + Real.log (1 + Real.exp s), ?_⟩
    rintro x ⟨j, rfl⟩
    simp only
    exact fc_edgeFE_le_const d (agl_K j) hd (agl_K_pos j) hq s (hbox j)
  obtain ⟨L', hL'⟩ := agl_subseq_almost_mono_converges
    (fun n => fc_edgeFreeEnergy d q s n) agl_K δ
    (fun j => mul_nonneg hMc0 (hIE0 j)) (hIsum.mul_left (M + c)) hmono hbdd
  refine ⟨Real.log (1 + Real.exp s) - L', ?_⟩
  have heq : ∀ j, fc_f d q s (agl_K j)
      = Real.log (1 + Real.exp s) - fc_edgeFreeEnergy d q s (agl_K j) := by
    intro j; rw [fc_f, fc_edgeFE_eq, agl_E]; ring
  rw [show (fun j => fc_f d q s (agl_K j))
      = (fun j => Real.log (1 + Real.exp s) - fc_edgeFreeEnergy d q s (agl_K j)) from
    funext heq]
  have := (hL'.const_sub (Real.log (1 + Real.exp s)))
  simpa using this


theorem fc_f_lower (hd : 1 ≤ d) {q : ℝ} (hq : 1 ≤ q) (s : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hbox : ∀ k, 1 ≤ k → 0 < (boxGraph d k).edgeFinset.card) (L : ℝ)
    (hL : Tendsto (fun j => fc_f d q s (agl_K j)) atTop (𝓝 L)) :
    ((2 * (n : ℝ) + 1) / (2 * n)) * L - (-Real.log (1 - fsc_logistic s)) / (2 * n)
      ≤ fc_f d q s n := by
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
      fc_f d q s (agl_K j) ≤ rfun j * fc_f d q s n + (1 - rfun j) * c := by
    intro j hj
    have := fc_perEdge_vanHove (d := d) n (agl_K j) hq s (hbox (agl_K j) (agl_K_pos j)) (hbox n hn)
    rw [← hc] at this
    simpa [hrfun] using this
  have hrinf_pos : (0 : ℝ) < 2 * (n : ℝ) / (2 * n + 1) := by positivity
  have hRHS_tendsto : Tendsto (fun j => rfun j * fc_f d q s n + (1 - rfun j) * c) atTop
      (𝓝 ((2 * (n : ℝ) / (2 * n + 1)) * fc_f d q s n
          + (1 - 2 * (n : ℝ) / (2 * n + 1)) * c)) :=
    ((hr_tendsto.mul tendsto_const_nhds).add
      (((tendsto_const_nhds).sub hr_tendsto).mul tendsto_const_nhds))
  have hKge : ∀ᶠ j in atTop, n ≤ agl_K j := agl_K_tendsto_atTop.eventually_ge_atTop n
  have hLle : L ≤ (2 * (n : ℝ) / (2 * n + 1)) * fc_f d q s n + (1 - 2 * (n : ℝ) / (2 * n + 1)) * c := by
    refine le_of_tendsto_of_tendsto hL hRHS_tendsto ?_
    filter_upwards [hKge] with j hj using hbound j hj
  set R : ℝ := 2 * (n : ℝ) / (2 * n + 1) with hR
  have hRpos : 0 < R := hrinf_pos
  have h2n1 : (0:ℝ) < 2 * (n:ℝ) + 1 := by positivity
  have hfn : (L - (1 - R) * c) / R ≤ fc_f d q s n := by
    rw [div_le_iff₀ hRpos]; nlinarith [hLle]
  have hsimp : (L - (1 - R) * c) / R
      = (2 * (n : ℝ) + 1) / (2 * n) * L - c / (2 * n) := by
    rw [hR]; field_simp; ring
  rw [hsimp] at hfn
  linarith [hfn]


end Walls
end StatMech
