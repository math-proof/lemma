/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingExponentialPlus.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.IsingSusceptibilityPlus.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.IsingSharpness
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped BigOperators StatMech


namespace StatMech

namespace Sharpness

open Ising (spin plusState spin_eq_pm spin_sq boxFinset mem_boxFinset)

open Lattice Percolation ConfigSpace

variable {d : ℕ}


theorem ae_spin_eq_of_plusCorr_eq_one (beta : ℝ) (x y : Site d)
    (hxy : plusCorr d beta x y = 1) :
    ∀ᵐ omega ∂(plusState d beta 0 : Measure (ConfigSpace (Site d))),
      spin omega x = spin omega y := by
  let mu : Measure (ConfigSpace (Site d)) := plusState d beta 0
  haveI : IsProbabilityMeasure mu := (plusState d beta 0).2
  have hpair : Integrable
      (fun omega : ConfigSpace (Site d) => spin omega x * spin omega y) mu := by
    change Integrable (spinPairBCF x y) mu
    exact (spinPairBCF x y).integrable mu
  have hint : Integrable
      (fun omega : ConfigSpace (Site d) =>
        1 - spin omega x * spin omega y) mu :=
    (integrable_const 1).sub hpair
  have hnonneg : 0 ≤ᵐ[mu]
      (fun omega : ConfigSpace (Site d) =>
        1 - spin omega x * spin omega y) := by
    filter_upwards with omega
    rcases spin_eq_pm omega x with hx | hx <;>
      rcases spin_eq_pm omega y with hy | hy <;> rw [hx, hy] <;> norm_num
  have hzero : ∫ omega, (1 - spin omega x * spin omega y) ∂mu = 0 := by
    rw [integral_sub (integrable_const 1) hpair]
    simp only [integral_const, probReal_univ, one_smul]
    exact sub_eq_zero.mpr (by simpa [mu, plusCorr] using hxy.symm)
  have hae :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae hnonneg hint).mp hzero
  filter_upwards [hae] with omega homega
  simp only [Pi.zero_apply] at homega
  rcases spin_eq_pm omega x with hx | hx <;>
    rcases spin_eq_pm omega y with hy | hy <;> simp_all

theorem site_nsmul_injective {x : Site d} (hx : x ≠ 0) :
    Function.Injective (fun n : ℕ => n • x) := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    simpa [Function.ne_iff] using hx
  intro n m hnm
  have hcoord := congrFun hnm i
  change (n : ℤ) * x i = (m : ℤ) * x i at hcoord
  have hcast : (n : ℤ) = (m : ℤ) := mul_right_cancel₀ hi hcoord
  exact_mod_cast hcast


theorem plusCorr_eq_one_multiples (beta : ℝ) (hbeta : 0 ≤ beta)
    {x : Site d} (hxone : plusCorr d beta (origin d) x = 1) :
    ∀ n : ℕ, plusCorr d beta (origin d) (n • x) = 1 := by
  have hstep : ∀ n : ℕ,
      ∀ᵐ omega ∂(plusState d beta 0 : Measure (ConfigSpace (Site d))),
        spin omega (n • x) = spin omega ((n + 1) • x) := by
    intro n
    apply ae_spin_eq_of_plusCorr_eq_one beta
    rw [plusCorr_eq_origin_translate beta hbeta]
    have hdiff : (n + 1) • x - n • x = x := by
      ext i
      change ((n + 1 : ℕ) : ℤ) * x i - (n : ℤ) * x i = x i
      push_cast
      ring
    rw [hdiff]
    exact hxone
  have hchain : ∀ n : ℕ,
      ∀ᵐ omega ∂(plusState d beta 0 : Measure (ConfigSpace (Site d))),
        spin omega (origin d) = spin omega (n • x) := by
    intro n
    induction n with
    | zero =>
        filter_upwards
        intro omega
        change spin omega (0 : Site d) = spin omega (0 • x)
        simp
    | succ n ih =>
        filter_upwards [ih, hstep n] with omega h0 hn
        exact h0.trans hn
  intro n
  unfold plusCorr
  haveI : IsProbabilityMeasure
      (plusState d beta 0 : Measure (ConfigSpace (Site d))) :=
    (plusState d beta 0).2
  calc
    (∫ omega, spin omega (origin d) * spin omega (n • x)
        ∂(plusState d beta 0 : Measure (ConfigSpace (Site d)))) =
        ∫ _omega, (1 : ℝ)
          ∂(plusState d beta 0 : Measure (ConfigSpace (Site d))) := by
      apply integral_congr_ae
      filter_upwards [hchain n] with omega homega
      rw [← homega, spin_sq]
    _ = 1 := by simp


theorem plusCorr_lt_one_of_summable (beta : ℝ) (hbeta : 0 ≤ beta)
    (hsum : Summable (plusCorr d beta (origin d)))
    {x : Site d} (hx : x ≠ origin d) :
    plusCorr d beta (origin d) x < 1 := by
  apply lt_of_le_of_ne (plusCorr_le_one beta _ _)
  intro heq
  have hx0 : x ≠ 0 := by simpa [origin] using hx
  have hone := plusCorr_eq_one_multiples beta hbeta heq
  have hseq : Summable (fun n : ℕ => plusCorr d beta (origin d) (n • x)) := by
    simpa only [Function.comp_apply] using
      hsum.comp_injective (site_nsmul_injective hx0)
  have hzero := hseq.tendsto_atTop_zero
  have hlim : Tendsto (fun _n : ℕ => (1 : ℝ)) atTop (nhds 0) := by
    simpa only [hone] using hzero
  have hone_lim : Tendsto (fun _n : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have h01 : (0 : ℝ) = 1 := tendsto_nhds_unique hlim hone_lim
  norm_num at h01

theorem l1dist_origin_sub (x y : Site d) :
    l1dist d (origin d) (x - y) = l1dist d y x := by
  unfold l1dist origin
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  simp only [Pi.sub_apply]
  ring

@[simp] theorem l1dist_origin_eq_zero_iff (z : Site d) :
    l1dist d (origin d) z = 0 ↔ z = origin d := by
  constructor
  · intro h
    unfold l1dist origin at h
    simp only [zero_sub, Int.natAbs_neg] at h
    ext i
    change z i = 0
    have hi : (z i).natAbs = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun j (_ : j ∈ Finset.univ) => Nat.zero_le (z j).natAbs)).mp h i
          (Finset.mem_univ i)
    exact Int.natAbs_eq_zero.mp hi
  · rintro rfl
    exact l1dist_self d (origin d)

theorem mem_boxFinset_of_l1dist_origin_le (N : ℕ) (z : Site d)
    (h : l1dist d (origin d) z ≤ N) : z ∈ Ising.boxFinset d N := by
  rw [Ising.mem_boxFinset, mem_box]
  intro i
  unfold l1dist origin at h
  simp only [zero_sub, Int.natAbs_neg] at h
  exact (Finset.single_le_sum
    (fun j (_ : j ∈ Finset.univ) => Nat.zero_le (z j).natAbs)
    (Finset.mem_univ i)).trans h


end Sharpness
end StatMech
