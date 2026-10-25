/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsContourCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.PeierlsContourClose.Part4
import Def.StatisticalMechanics.Code.Ising.PeierlsContourCount
open MeasureTheory Filter Topology Finset SimpleGraph
open scoped BigOperators ENNReal


namespace StatMech

namespace Ising

open StatMech.Lattice

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


theorem pcc_pairCluster_card_le (p : Site d) : (pcc_pairCluster p).card ≤ 2 :=
  le_trans (Finset.card_insert_le _ _) (by simp)


theorem pcc_pairCluster_contourLen_le (p : Site d) (n : ℕ) :
    contourLen (↑(pcc_pairCluster p)) (bondFinsetTouch d n) ≤ 2 * d * 2 :=
  le_trans (pcc_contourLen_le_card_mul (pcc_pairCluster p) n)
    (Nat.mul_le_mul_left _ (pcc_pairCluster_card_le p))


theorem pcc_pairCluster_injOn :
    Set.InjOn (pcc_pairCluster (d := d)) {p | p ≠ origin d} := by
  intro p hp q hq h
  unfold pcc_pairCluster at h
  have hpmem : p ∈ ({origin d, q} : Finset (Site d)) := by
    rw [← h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self p)
  rw [Finset.mem_insert, Finset.mem_singleton] at hpmem
  rcases hpmem with hpo | hpq
  · exact absurd hpo hp
  · exact hpq


theorem pcc_pairCluster_mem_originFamily {n : ℕ} {p : Site d} (hp : p ∈ boxFinset d n) :
    pcc_pairCluster p ∈ originClusterFamily (d := d) n := by
  rw [pcc_mem_originClusterFamily]
  refine ⟨?_, Finset.mem_insert_self _ _⟩
  unfold clusterFamily pcc_pairCluster
  rw [Finset.mem_powerset]
  intro x hx
  rw [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · rw [mem_boxFinset]; exact origin_mem_box n
  · exact hp


theorem pcc_originSum_ge (n : ℕ) (β : ℝ) (hβ : 0 ≤ β) :
    (((boxFinset d n).erase (origin d)).card : ℝ) * Real.exp (-(2 * β) * (2 * d * 2 : ℕ))
      ≤ ∑ K ∈ originClusterFamily (d := d) n,
          Real.exp (-(2 * β) * (contourLen (↑K) (bondFinsetTouch d n) : ℝ)) := by
  classical
  set S := (boxFinset d n).erase (origin d) with hS
  have himg_sub : S.image (pcc_pairCluster (d := d)) ⊆ originClusterFamily (d := d) n := by
    intro K hK
    rw [Finset.mem_image] at hK
    obtain ⟨p, hp, rfl⟩ := hK
    exact pcc_pairCluster_mem_originFamily (Finset.mem_of_mem_erase hp)
  have hsub : ∑ K ∈ S.image (pcc_pairCluster (d := d)),
        Real.exp (-(2 * β) * (contourLen (↑K) (bondFinsetTouch d n) : ℝ))
      ≤ ∑ K ∈ originClusterFamily (d := d) n,
          Real.exp (-(2 * β) * (contourLen (↑K) (bondFinsetTouch d n) : ℝ)) :=
    Finset.sum_le_sum_of_subset_of_nonneg himg_sub (fun _ _ _ => by positivity)
  refine le_trans ?_ hsub
  have hinj : Set.InjOn (pcc_pairCluster (d := d)) (S : Set (Site d)) := by
    apply pcc_pairCluster_injOn.mono
    intro p hp
    simp only [hS, Finset.coe_erase, Set.mem_diff, Finset.mem_coe, Set.mem_singleton_iff] at hp
    exact hp.2
  rw [Finset.sum_image (fun a ha b hb => hinj (by exact_mod_cast ha) (by exact_mod_cast hb))]
  calc (S.card : ℝ) * Real.exp (-(2 * β) * (2 * d * 2 : ℕ))
      = ∑ _p ∈ S, Real.exp (-(2 * β) * (2 * d * 2 : ℕ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ p ∈ S, Real.exp (-(2 * β) *
          (contourLen (↑(pcc_pairCluster p)) (bondFinsetTouch d n) : ℝ)) := by
        refine Finset.sum_le_sum (fun p _ => ?_)
        apply Real.exp_le_exp.mpr
        have hle : (contourLen (↑(pcc_pairCluster p)) (bondFinsetTouch d n) : ℝ)
            ≤ (2 * d * 2 : ℕ) := by exact_mod_cast pcc_pairCluster_contourLen_le p n
        have h2β : 0 ≤ 2 * β := by linarith
        nlinarith [hle, h2β]


theorem pcc_rayS_coord (c : Fin d) (j : ℕ) : (pcc_rayS c j) c = (j : ℤ) := by
  unfold pcc_rayS; simp


theorem pcc_rayS_ne_origin (c : Fin d) {j : ℕ} (hj : 0 < j) : pcc_rayS c j ≠ origin d := by
  intro h
  have hc : (pcc_rayS c j) c = (origin d) c := by rw [h]
  rw [pcc_rayS_coord] at hc
  unfold origin at hc
  omega


theorem pcc_n_le_erase_card (hd : 1 ≤ d) (n : ℕ) :
    n ≤ ((boxFinset d n).erase (origin d)).card := by
  classical
  set c : Fin d := ⟨0, hd⟩
  have hmap : ∀ j : Fin n, pcc_rayS c (j + 1) ∈ (boxFinset d n).erase (origin d) := by
    intro j
    rw [Finset.mem_erase]
    refine ⟨pcc_rayS_ne_origin c (by omega), ?_⟩
    rw [mem_boxFinset]
    exact pcc_rayS_mem_box_le c (j + 1) n (by omega)
  have hinj : Function.Injective (fun j : Fin n => pcc_rayS c (j + 1)) := by
    intro i j h
    simp only at h
    have hc : (pcc_rayS c (i + 1)) c = (pcc_rayS c (j + 1)) c := by rw [h]
    rw [pcc_rayS_coord, pcc_rayS_coord] at hc
    have : (i : ℕ) + 1 = (j : ℕ) + 1 := by exact_mod_cast hc
    exact Fin.ext (by omega)
  calc n = (Finset.univ : Finset (Fin n)).card := by rw [Finset.card_univ, Fintype.card_fin]
    _ = (Finset.univ.image (fun j : Fin n => pcc_rayS c (j + 1))).card := by
        rw [Finset.card_image_of_injective _ hinj]
    _ ≤ ((boxFinset d n).erase (origin d)).card := by
        refine Finset.card_le_card (fun x hx => ?_)
        rw [Finset.mem_image] at hx
        obtain ⟨j, _, rfl⟩ := hx
        exact hmap j


theorem pcc_originSum_unbounded (hd : 1 ≤ d) (β : ℝ) (hβ : 0 ≤ β) (M : ℝ) :
    ∃ n : ℕ, M < ∑ K ∈ originClusterFamily (d := d) n,
        Real.exp (-(2 * β) * (contourLen (↑K) (bondFinsetTouch d n) : ℝ)) := by
  set c0 : ℝ := Real.exp (-(2 * β) * (2 * d * 2 : ℕ)) with hc0
  have hc0pos : 0 < c0 := Real.exp_pos _
  
  obtain ⟨n, hn⟩ := exists_nat_gt (M / c0)
  refine ⟨n, ?_⟩
  have hlb := pcc_originSum_ge (d := d) n β hβ
  have hcard : (n : ℝ) ≤ (((boxFinset d n).erase (origin d)).card : ℝ) := by
    exact_mod_cast pcc_n_le_erase_card hd n
  have hstep : (n : ℝ) * c0 ≤ (((boxFinset d n).erase (origin d)).card : ℝ) * c0 :=
    mul_le_mul_of_nonneg_right hcard hc0pos.le
  have hMlt : M < (n : ℝ) * c0 := by
    rw [div_lt_iff₀ hc0pos] at hn; linarith
  calc M < (n : ℝ) * c0 := hMlt
    _ ≤ (((boxFinset d n).erase (origin d)).card : ℝ) * c0 := hstep
    _ ≤ _ := hlb


theorem pcc_not_originContourCountBound (hd : 1 ≤ d) (β : ℝ) (hβ : 0 ≤ β) :
    ∃ n : ℕ, ¬ OriginContourCountBound d n β := by
  obtain ⟨n, hn⟩ := pcc_originSum_unbounded hd β hβ (peierlsBound d β)
  exact ⟨n, fun hCount => absurd (lt_of_lt_of_le hn hCount) (lt_irrefl _)⟩


theorem pcc_originContourCount_hypothesis_false (hd : 1 ≤ d) :
    ¬ ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β → OriginContourCountBound d n β := by
  rintro ⟨β₀, hβ₀⟩
  set β : ℝ := max β₀ 0 with hβdef
  obtain ⟨n, hn⟩ := pcc_not_originContourCountBound (d := d) hd β (le_max_right _ _)
  exact hn (hβ₀ n β (le_max_left _ _))


end Ising
end StatMech
