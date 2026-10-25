/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKilledKernel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedWalk.Part6
import Def.StatisticalMechanics.Code.Universality.IsingFermionicKilledKernel.Part2


namespace StatMech.Universality

open Finset

noncomputable section

theorem isingLeapfrogExitKernel_tendsto_limit (R : Nat)
    (p q : IsingLeapfrogBox R) :
    Filter.Tendsto (fun t ↦ isingLeapfrogExitKernel R t p q)
      Filter.atTop (nhds (isingLeapfrogExitKernelLimit R p q)) := by
  apply tendsto_atTop_ciSup (isingLeapfrogExitKernel_mono R p q)
  refine ⟨1, ?_⟩
  rintro _ ⟨t, rfl⟩
  exact isingLeapfrogExitKernel_le_one R t p q

theorem isingLeapfrogExitKernel_succ (R t : Nat)
    (p q : IsingLeapfrogBox R) :
    isingLeapfrogExitKernel R (t + 1) p q =
      if hp : isingLeapfrogBoxBoundary R p then
        isingLeapfrogExitKernel R t p q
      else
        (isingLeapfrogExitKernel R t (isingLeapfrogSW R p) q +
          isingLeapfrogExitKernel R t (isingLeapfrogSE R p hp) q +
          isingLeapfrogExitKernel R t (isingLeapfrogNW R p hp) q +
          isingLeapfrogExitKernel R t (isingLeapfrogNE R p hp) q) / 4 := by
  by_cases hq : isingLeapfrogBoxBoundary R q
  · unfold isingLeapfrogExitKernel
    simp only [if_pos hq]
    exact isingLeapfrogStoppedKernel_succ R t p q
  · simp [isingLeapfrogExitKernel, hq]


theorem isingLeapfrogExitKernel_succ_sub (R t : Nat)
    (p q : IsingLeapfrogBox R) (hq : isingLeapfrogBoxBoundary R q) :
    isingLeapfrogExitKernel R (t + 1) p q -
        isingLeapfrogExitKernel R t p q =
      ∑ r, isingLeapfrogKilledKernel R t p r *
        isingLeapfrogStoppedKernel R 1 r q := by
  classical
  have hadd := isingLeapfrogStoppedKernel_add R t 1 p q
  have hexit : (∑ r, isingLeapfrogExitKernel R t p r *
      isingLeapfrogStoppedKernel R 1 r q) =
      isingLeapfrogExitKernel R t p q := by
    calc
      _ = ∑ r, if r = q then isingLeapfrogExitKernel R t p r else 0 := by
        apply Finset.sum_congr rfl
        intro r hr
        by_cases hbr : isingLeapfrogBoxBoundary R r
        · rw [isingLeapfrogStoppedKernel_of_boundary R 1 r q hbr]
          simp [hbr]
        · have hrq : r ≠ q := fun hrq ↦ hbr (hrq ▸ hq)
          simp [isingLeapfrogExitKernel, hbr, hrq]
      _ = _ := by simp
  have hsplit : (∑ r, isingLeapfrogStoppedKernel R t p r *
      isingLeapfrogStoppedKernel R 1 r q) =
      (∑ r, isingLeapfrogKilledKernel R t p r *
        isingLeapfrogStoppedKernel R 1 r q) +
      ∑ r, isingLeapfrogExitKernel R t p r *
        isingLeapfrogStoppedKernel R 1 r q := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    rw [← add_mul,
      ← isingLeapfrogStoppedKernel_eq_killed_add_exit R t p r]
  rw [hsplit, hexit] at hadd
  have hexit_eq : isingLeapfrogExitKernel R t p q =
      isingLeapfrogStoppedKernel R t p q := by
    simp [isingLeapfrogExitKernel, hq]
  rw [hexit_eq] at hadd
  unfold isingLeapfrogExitKernel
  simp only [if_pos hq] at hadd ⊢
  linarith


theorem isingLeapfrogExitKernel_eq_sum_flux (R t : Nat)
    (p q : IsingLeapfrogBox R)
    (hp : ¬ isingLeapfrogBoxBoundary R p)
    (hq : isingLeapfrogBoxBoundary R q) :
    isingLeapfrogExitKernel R t p q =
      ∑ s ∈ range t, ∑ r, isingLeapfrogKilledKernel R s p r *
        isingLeapfrogStoppedKernel R 1 r q := by
  induction t with
  | zero =>
      have hpq : p ≠ q := fun hpq ↦ hp (hpq ▸ hq)
      simp [isingLeapfrogExitKernel, isingLeapfrogStoppedKernel, hq, hpq]
  | succ t ih =>
      rw [Finset.sum_range_succ, ← ih]
      have hflux := isingLeapfrogExitKernel_succ_sub R t p q hq
      linarith


theorem isingLeapfrogExitKernelLimit_meanValue (R : Nat)
    (p q : IsingLeapfrogBox R)
    (hp : ¬ isingLeapfrogBoxBoundary R p) :
    isingLeapfrogExitKernelLimit R (isingLeapfrogSW R p) q +
        isingLeapfrogExitKernelLimit R (isingLeapfrogSE R p hp) q +
        isingLeapfrogExitKernelLimit R (isingLeapfrogNW R p hp) q +
        isingLeapfrogExitKernelLimit R (isingLeapfrogNE R p hp) q =
      4 * isingLeapfrogExitKernelLimit R p q := by
  have hP := (isingLeapfrogExitKernel_tendsto_limit R p q).comp
    (Filter.tendsto_add_atTop_nat 1)
  have hSW := isingLeapfrogExitKernel_tendsto_limit R
    (isingLeapfrogSW R p) q
  have hSE := isingLeapfrogExitKernel_tendsto_limit R
    (isingLeapfrogSE R p hp) q
  have hNW := isingLeapfrogExitKernel_tendsto_limit R
    (isingLeapfrogNW R p hp) q
  have hNE := isingLeapfrogExitKernel_tendsto_limit R
    (isingLeapfrogNE R p hp) q
  have hAvg := (((hSW.add hSE).add hNW).add hNE).div_const 4
  have hrec : (fun t ↦ isingLeapfrogExitKernel R (t + 1) p q) =
      fun t ↦ (isingLeapfrogExitKernel R t (isingLeapfrogSW R p) q +
        isingLeapfrogExitKernel R t (isingLeapfrogSE R p hp) q +
        isingLeapfrogExitKernel R t (isingLeapfrogNW R p hp) q +
        isingLeapfrogExitKernel R t (isingLeapfrogNE R p hp) q) / 4 := by
    funext t
    rw [isingLeapfrogExitKernel_succ]
    simp only [dif_neg hp]
  change Filter.Tendsto (fun t ↦
    isingLeapfrogExitKernel R (t + 1) p q) Filter.atTop _ at hP
  rw [hrec] at hP
  have hlim := tendsto_nhds_unique hP hAvg
  linarith

theorem isingLeapfrogExitKernel_sum_eq_boundaryMass (R t : Nat)
    (p : IsingLeapfrogBox R) :
    ∑ q, isingLeapfrogExitKernel R t p q =
      isingLeapfrogStoppedBoundaryMass R t p := by
  classical
  unfold isingLeapfrogExitKernel isingLeapfrogStoppedBoundaryMass
  rw [Finset.sum_filter]

theorem isingLeapfrogKilledKernel_sum_add_boundaryMass_eq_one
    (R t : Nat) (p : IsingLeapfrogBox R) :
    (∑ q, isingLeapfrogKilledKernel R t p q) +
        isingLeapfrogStoppedBoundaryMass R t p = 1 := by
  classical
  rw [← isingLeapfrogExitKernel_sum_eq_boundaryMass]
  rw [← Finset.sum_add_distrib]
  simp_rw [← isingLeapfrogStoppedKernel_eq_killed_add_exit]
  exact isingLeapfrogStoppedKernel_sum_eq_one R t p


end
end StatMech.Universality
