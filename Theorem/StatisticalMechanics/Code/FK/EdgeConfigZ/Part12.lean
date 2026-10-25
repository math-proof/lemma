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
import Def.StatisticalMechanics.Code.FK.EdgeConfigZ.Part13
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


theorem ecz_box_vanHove_subadd (m n : ℕ) (t : ℝ) :
    ecz_u d t n ≤ ((ecz_T m n) ^ d : ℝ) * ecz_u d t m
      + (((boxGraph d n).edgeFinset.card : ℝ)
          - ((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ))
          * (-Real.log (1 - fsc_logistic t)) := by
  classical
  set p := fsc_logistic t with hp
  have hp0 : (0 : ℝ) < p := fsc_logistic_pos t
  have hp1 : p < 1 := fsc_logistic_lt_one t
  set c := -Real.log (1 - p) with hc
  have hc0 : 0 ≤ c := by rw [hc, neg_nonneg]; exact Real.log_nonpos (by linarith) (by linarith)
  set tag := ecz_vanHoveTag m n with htag
  set K₀ := boxGraph d n with hK₀
  
  have hsub := ecz_multiblock_subadd K₀ tag p 2 hp0 hp1 (by norm_num : (0:ℝ) < 2) Finset.univ
  
  have hrest_u : ecz_uu (qp_restG K₀ tag Finset.univ) p 2 = ecz_u d t n := by
    rw [ecz_uu, ecz_u, hp, ecz_fkZEdge_iso (ecz_restUnivIso m n) p 2]
  have hrest_E : ((qp_restG K₀ tag Finset.univ).edgeFinset.card : ℝ)
      = ((boxGraph d n).edgeFinset.card : ℝ) := by
    rw [(ecz_restUnivIso m n).card_edgeFinset_eq]
  
  have hsplit_u : (∑ τ : Option (Fin d → Fin (ecz_T m n)), ecz_uu (qp_blkG K₀ tag τ) p 2)
      = ecz_uu (qp_blkG K₀ tag none) p 2
        + ((ecz_T m n) ^ d : ℝ) * ecz_u d t m := by
    rw [Fintype.sum_option]
    congr 1
    have heach : ∀ c : Fin d → Fin (ecz_T m n),
        ecz_uu (qp_blkG K₀ tag (some c)) p 2 = ecz_u d t m := fun c => by
      rw [ecz_uu, ecz_u, hp, ecz_cellBlock_fkZEdge m n c]
    rw [Finset.sum_congr rfl (fun c _ => heach c), Finset.sum_const, Finset.card_univ,
      ecz_cell_card, nsmul_eq_mul]
    push_cast; ring
  have hsplit_E : (∑ τ : Option (Fin d → Fin (ecz_T m n)),
        ((qp_blkG K₀ tag τ).edgeFinset.card : ℝ))
      = ((qp_blkG K₀ tag none).edgeFinset.card : ℝ)
        + ((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ) := by
    rw [Fintype.sum_option]
    congr 1
    have heach : ∀ c : Fin d → Fin (ecz_T m n),
        ((qp_blkG K₀ tag (some c)).edgeFinset.card : ℝ) = ((boxGraph d m).edgeFinset.card : ℝ) :=
      fun c => by rw [ecz_cellBlock_edge_card m n c]
    rw [Finset.sum_congr rfl (fun c _ => heach c), Finset.sum_const, Finset.card_univ,
      ecz_cell_card, nsmul_eq_mul]
    push_cast; ring
  
  have hnone : ecz_uu (qp_blkG K₀ tag none) p 2
      ≤ ((qp_blkG K₀ tag none).edgeFinset.card : ℝ) * c := by
    rw [ecz_uu, hc]; exact ecz_neglogZEdge_le_edges _ hp0 hp1 (by norm_num : (1:ℝ) ≤ 2)
  
  rw [show (∑ τ ∈ (Finset.univ : Finset (Option (Fin d → Fin (ecz_T m n)))),
        ecz_uu (qp_blkG K₀ tag τ) p 2)
      = ∑ τ : Option (Fin d → Fin (ecz_T m n)), ecz_uu (qp_blkG K₀ tag τ) p 2 from rfl] at hsub
  rw [show (∑ τ ∈ (Finset.univ : Finset (Option (Fin d → Fin (ecz_T m n)))),
        ((qp_blkG K₀ tag τ).edgeFinset.card : ℝ))
      = ∑ τ : Option (Fin d → Fin (ecz_T m n)), ((qp_blkG K₀ tag τ).edgeFinset.card : ℝ) from rfl]
    at hsub
  rw [hrest_u, hsplit_u, hrest_E, hsplit_E] at hsub
  
  set uNone : ℝ := ecz_uu (qp_blkG K₀ tag none) p 2 with huNone
  set ENone : ℝ := ((qp_blkG K₀ tag none).edgeFinset.card : ℝ) with hENone
  set Td : ℝ := ((ecz_T m n) ^ d : ℝ) with hTd
  set Um : ℝ := ecz_u d t m with hUm
  set Em : ℝ := ((boxGraph d m).edgeFinset.card : ℝ) with hEm
  set En : ℝ := ((boxGraph d n).edgeFinset.card : ℝ) with hEn
  
  
  
  have hexpand : (En - (ENone + Td * Em)) * c = (En - Td * Em) * c - ENone * c := by ring
  rw [hexpand] at hsub
  linarith [hsub, hnone]


theorem ecz_denom_tendsto_atTop :
    Tendsto (fun n : ℕ => (2 * (n : ℝ) + 1)) atTop atTop := by
  apply Filter.tendsto_atTop_add_const_right
  exact Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop


theorem ecz_packing_ratio_tendsto (m : ℕ) :
    Tendsto (fun n => ((ecz_T m n : ℝ) * (2 * m + 1)) / (2 * n + 1)) atTop (𝓝 1) := by
  have hupper : ∀ n, ((ecz_T m n : ℝ) * (2 * m + 1)) / (2 * n + 1) ≤ 1 := by
    intro n
    have hden : (0 : ℝ) < 2 * n + 1 := by positivity
    rw [div_le_one hden]
    have : (ecz_T m n * (2 * m + 1) : ℕ) ≤ 2 * n + 1 := ecz_T_mul_le m n
    exact_mod_cast this
  have h0 : Tendsto (fun n : ℕ => (2 * (m : ℝ) + 1) / (2 * n + 1)) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := (2 * (m : ℝ) + 1))).div_atTop ecz_denom_tendsto_atTop
  have hlowfun : Tendsto (fun n : ℕ => 1 - (2 * (m : ℝ) + 1) / (2 * n + 1)) atTop (𝓝 1) := by
    have := h0.const_sub (1 : ℝ); simpa using this
  have hlower : ∀ n : ℕ, 1 - (2 * (m : ℝ) + 1) / (2 * n + 1)
      ≤ ((ecz_T m n : ℝ) * (2 * m + 1)) / (2 * n + 1) := by
    intro n
    have hden : (0 : ℝ) < 2 * n + 1 := by positivity
    
    have hT1 : 2 * n + 1 < (ecz_T m n + 1) * (2 * m + 1) := by
      have hdm := Nat.div_add_mod (2 * n + 1) (2 * m + 1)
      have hmod := Nat.mod_lt (2 * n + 1) (show 0 < 2 * m + 1 by omega)
      rw [ecz_T]; nlinarith [hdm, hmod]
    have hT1R : (2 * (n : ℝ) + 1) < ((ecz_T m n : ℝ) + 1) * (2 * m + 1) := by
      have : ((2 * n + 1 : ℕ) : ℝ) < (((ecz_T m n + 1) * (2 * m + 1) : ℕ) : ℝ) := by
        exact_mod_cast hT1
      push_cast at this ⊢; linarith
    rw [le_div_iff₀ hden, sub_mul, div_mul_cancel₀ _ (ne_of_gt hden)]
    nlinarith [hT1R]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlowfun tendsto_const_nhds hlower hupper


theorem ecz_oddEven_ratio_tendsto :
    Tendsto (fun n : ℕ => (2 * (n : ℝ) + 1) / (2 * n)) atTop (𝓝 1) := by
  have hden : Tendsto (fun n : ℕ => (2 * (n : ℝ))) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
  have h0 : Tendsto (fun n : ℕ => 1 / (2 * (n : ℝ))) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := (1 : ℝ))).div_atTop hden
  have heq : ∀ n : ℕ, 1 ≤ n → (2 * (n : ℝ) + 1) / (2 * n) = 1 + 1 / (2 * n) := by
    intro n hn
    have hden0 : (0 : ℝ) < 2 * n := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      positivity
    field_simp
  have hlim : Tendsto (fun n : ℕ => 1 + 1 / (2 * (n : ℝ))) atTop (𝓝 1) := by
    have := h0.const_add (1 : ℝ); simpa using this
  refine (Filter.tendsto_congr' ?_).mpr hlim
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn using (heq n hn)


theorem ecz_bulkFraction_tendsto (hd : 1 ≤ d) (m : ℕ) (hm : 1 ≤ m) :
    Tendsto (fun n => ((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ)
        / ((boxGraph d n).edgeFinset.card : ℝ)) atTop
      (𝓝 (2 * (m : ℝ) / (2 * m + 1))) := by
  
  have hprod : Tendsto (fun n => (((ecz_T m n : ℝ) * (2 * m + 1)) / (2 * n + 1)) ^ d
        * (2 * (m : ℝ) / (2 * m + 1)) * ((2 * (n : ℝ) + 1) / (2 * n))) atTop
      (𝓝 ((1 : ℝ) ^ d * (2 * (m : ℝ) / (2 * m + 1)) * 1)) := by
    refine ((((ecz_packing_ratio_tendsto m).pow d).mul tendsto_const_nhds).mul
      ecz_oddEven_ratio_tendsto)
  rw [one_pow, one_mul, mul_one] at hprod
  refine (Filter.tendsto_congr' ?_).mp hprod
  
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hnpos : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hM1 : (0 : ℝ) < 2 * m + 1 := by positivity
  have h2n : (0 : ℝ) < 2 * n := by positivity
  have h2n1 : (0 : ℝ) < 2 * n + 1 := by positivity
  
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  
  have hEm : ((boxGraph (e + 1) m).edgeFinset.card : ℝ)
      = ((e : ℝ) + 1) * (2 * m) * (2 * (m : ℝ) + 1) ^ e := by
    rw [EdgeCount.boxGraph_edgeCard (e + 1) m hd]; push_cast; ring_nf
  have hEn : ((boxGraph (e + 1) n).edgeFinset.card : ℝ)
      = ((e : ℝ) + 1) * (2 * n) * (2 * (n : ℝ) + 1) ^ e := by
    rw [EdgeCount.boxGraph_edgeCard (e + 1) n hd]; push_cast; ring_nf
  rw [hEm, hEn, div_pow, mul_pow, pow_succ (2 * (m : ℝ) + 1) e, pow_succ (2 * (n : ℝ) + 1) e]
  have hpowMp : (0 : ℝ) < (2 * (m : ℝ) + 1) ^ e := by positivity
  have hpowNp : (0 : ℝ) < (2 * (n : ℝ) + 1) ^ e := by positivity
  have hepos : (0 : ℝ) < (e : ℝ) + 1 := by positivity
  field_simp


end VanHove
end BoxNesting
end FK
end StatMech
