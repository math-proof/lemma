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
import Def.StatisticalMechanics.Code.Sharpness.IsingExponentialPlus.Part2
open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped BigOperators StatMech


namespace StatMech

namespace Sharpness

open Ising (spin plusState spin_eq_pm spin_sq boxFinset mem_boxFinset)

open Lattice Percolation ConfigSpace

variable {d : ℕ}


theorem plusCorrTailSet_nonempty (beta : ℝ) (n : ℕ) :
    (plusCorrTailSet d beta n).Nonempty := ⟨0, Set.mem_insert 0 _⟩

theorem plusCorrTailSet_bddAbove (beta : ℝ) (n : ℕ) :
    BddAbove (plusCorrTailSet d beta n) := by
  refine ⟨1, ?_⟩
  rintro r (rfl | ⟨z, _, rfl⟩)
  · norm_num
  · exact plusCorr_le_one beta _ _

theorem plusCorr_le_tailSup (beta : ℝ) (n : ℕ) (z : Site d)
    (hz : n ≤ l1dist d (origin d) z) :
    plusCorr d beta (origin d) z ≤ plusCorrTailSup d beta n := by
  apply le_csSup (plusCorrTailSet_bddAbove (d := d) beta n)
  exact Set.mem_insert_iff.mpr (Or.inr ⟨z, hz, rfl⟩)

theorem plusCorrTailSup_nonneg (beta : ℝ) (n : ℕ) :
    0 ≤ plusCorrTailSup d beta n := by
  apply le_csSup (plusCorrTailSet_bddAbove (d := d) beta n)
  exact Set.mem_insert 0 _

theorem plusCorrTailSup_le_one (beta : ℝ) (n : ℕ) :
    plusCorrTailSup d beta n ≤ 1 := by
  unfold plusCorrTailSup
  apply csSup_le (plusCorrTailSet_nonempty (d := d) beta n)
  rintro r (rfl | ⟨z, _, rfl⟩)
  · norm_num
  · exact plusCorr_le_one beta _ _

theorem shifted_distance_ge {n R : ℕ} {y z : Site d}
    (hy : l1dist d (origin d) y < R)
    (hz : n + R ≤ l1dist d (origin d) z) :
    n ≤ l1dist d (origin d) (z - y) := by
  have htri := l1dist_triangle d (origin d) y z
  rw [← l1dist_origin_sub (d := d) z y] at htri
  omega


theorem plusCorrTailSup_step
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (T : Finset (Site d)) (ho : origin d ∈ T)
    (n : ℕ) (hn : 0 < n) :
    plusCorrTailSup d beta (n + isingSimonRadius d T) ≤
      phiIsing d beta T * plusCorrTailSup d beta n := by
  unfold plusCorrTailSup
  apply csSup_le (plusCorrTailSet_nonempty (d := d) beta
    (n + isingSimonRadius d T))
  rintro r (rfl | ⟨z, hz, rfl⟩)
  · exact mul_nonneg (phiIsing_nonneg d hbeta T)
      (plusCorrTailSup_nonneg (d := d) beta n)
  · have hzT : z ∉ T := by
      intro hzmem
      have hlt := cut_lt_isingSimonRadius (d := d) T hzmem
      omega
    calc
      plusCorr d beta (origin d) z ≤
          simonBoundaryPlus beta T (origin d) z :=
        plusCorr_simon beta hbeta T ho z hzT
      _ ≤ ∑ e ∈ boundaryEdges d T,
          (Real.tanh beta * corrOriginInner d beta T e.1) *
            plusCorrTailSup d beta n := by
        unfold simonBoundaryPlus
        apply Finset.sum_le_sum
        intro e he
        apply mul_le_mul_of_nonneg_left
        · rw [plusCorr_eq_origin_translate beta hbeta]
          apply plusCorr_le_tailSup beta n
          apply shifted_distance_ge
          · exact boundary_lt_isingSimonRadius (d := d) T he
          · exact hz
        · apply mul_nonneg
          · rw [Real.tanh_eq_sinh_div_cosh]
            exact div_nonneg (Real.sinh_nonneg_iff.mpr hbeta)
              (Real.cosh_pos _).le
          · exact corrOriginInner_nonneg d hbeta T e.1
      _ = phiIsing d beta T * plusCorrTailSup d beta n := by
        unfold phiIsing
        rw [Finset.mul_sum, ← Finset.sum_mul]


theorem plusCorrTailSup_geom
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (T : Finset (Site d)) (ho : origin d ∈ T) :
    ∀ k : ℕ,
      plusCorrTailSup d beta (k * isingSimonRadius d T + 1) ≤
        (phiIsing d beta T) ^ k := by
  intro k
  induction k with
  | zero => simpa using plusCorrTailSup_le_one (d := d) beta 1
  | succ k ih =>
      rw [Nat.succ_mul]
      have hs := plusCorrTailSup_step beta hbeta T ho
        (k * isingSimonRadius d T + 1) (by omega)
      calc
        plusCorrTailSup d beta
            (k * isingSimonRadius d T + isingSimonRadius d T + 1) ≤
          phiIsing d beta T *
            plusCorrTailSup d beta (k * isingSimonRadius d T + 1) := by
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
        _ ≤ phiIsing d beta T * (phiIsing d beta T) ^ k :=
          mul_le_mul_of_nonneg_left ih (phiIsing_nonneg d hbeta T)
        _ = (phiIsing d beta T) ^ (k + 1) := by rw [pow_succ]; ring


theorem plusCorr_exponential_of_phi_lt_one
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (T : Finset (Site d)) (ho : origin d ∈ T)
    (hphi0 : 0 < phiIsing d beta T) (hphi1 : phiIsing d beta T < 1) :
    ∃ c > 0, ∃ C > 0, ∀ z : Site d,
      plusCorr d beta (origin d) z ≤
        C * Real.exp (-c * l1dist d (origin d) z) := by
  let R := isingSimonRadius d T
  let phi := phiIsing d beta T
  refine ⟨-(Real.log phi / R), ?_, 1 / phi, by positivity, ?_⟩
  · have hlog : Real.log phi < 0 := Real.log_neg hphi0 hphi1
    have hR : (0 : ℝ) < R := by exact_mod_cast isingSimonRadius_pos (d := d) T
    exact neg_pos.mpr (div_neg_of_neg_of_pos hlog hR)
  · intro z
    let r := l1dist d (origin d) z
    by_cases hr : r = 0
    ·
      have hle := plusCorr_le_one beta (origin d) z
      have hone : (1 : ℝ) ≤ 1 / phi := by
        rw [le_div_iff₀ hphi0]
        simpa using hphi1.le
      rw [show l1dist d (origin d) z = 0 from hr]
      simp only [Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, mul_one]
      exact hle.trans hone
    · let k := (r - 1) / R
      have hthreshold : k * R + 1 ≤ r := by
        dsimp [k]
        have hR := isingSimonRadius_pos (d := d) T
        exact Nat.add_one_le_iff.mpr (by
          have := Nat.div_mul_le_self (r - 1) R
          omega)
      have htail := plusCorr_le_tailSup beta (k * R + 1) z hthreshold
      have hgeom := plusCorrTailSup_geom beta hbeta T ho k
      have hbridge := IsingSharp.geometric_le_exp R
        (isingSimonRadius_pos (d := d) T) phi hphi0 hphi1 r
      calc
        plusCorr d beta (origin d) z ≤ plusCorrTailSup d beta (k * R + 1) := htail
        _ ≤ phi ^ k := hgeom
        _ ≤ (1 / phi) * Real.exp ((Real.log phi / R) * r) := by
          simpa [k] using hbridge
        _ = (1 / phi) * Real.exp (-(-(Real.log phi / R)) * r) := by
          congr 2
          ring

theorem plusCorr_exponential_of_phi_eq_zero
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (T : Finset (Site d)) (ho : origin d ∈ T)
    (hphi : phiIsing d beta T = 0) :
    ∃ c > 0, ∃ C > 0, ∀ z : Site d,
      plusCorr d beta (origin d) z ≤
        C * Real.exp (-c * l1dist d (origin d) z) := by
  let R := isingSimonRadius d T
  have hstep := plusCorrTailSup_step beta hbeta T ho 1 (by omega)
  rw [hphi, zero_mul] at hstep
  have htail0 : plusCorrTailSup d beta (1 + R) = 0 :=
    le_antisymm hstep (plusCorrTailSup_nonneg (d := d) beta (1 + R))
  refine ⟨1, by norm_num, Real.exp ((R : ℝ) + 1), Real.exp_pos _, ?_⟩
  intro z
  let r := l1dist d (origin d) z
  by_cases hr : 1 + R ≤ r
  · have hz0 : plusCorr d beta (origin d) z = 0 := by
      apply le_antisymm
      · exact (plusCorr_le_tailSup beta (1 + R) z hr).trans_eq htail0
      · exact plusCorr_nonneg beta hbeta _ _
    rw [hz0]
    positivity
  · have hrle : r ≤ R := by omega
    calc
      plusCorr d beta (origin d) z ≤ 1 := plusCorr_le_one beta _ _
      _ ≤ Real.exp ((R : ℝ) + 1) * Real.exp (-(1 : ℝ) * r) := by
        rw [← Real.exp_add]
        apply Real.one_le_exp_iff.mpr
        have hcast : (r : ℝ) ≤ (R : ℝ) + 1 := by
          exact_mod_cast (show r ≤ R + 1 by omega)
        linarith


theorem plusCorr_exponential_of_witness
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (T : Finset (Site d)) (ho : origin d ∈ T)
    (hphi : phiIsing d beta T < 1) :
    ∃ c > 0, ∃ C > 0, ∀ z : Site d,
      plusCorr d beta (origin d) z ≤
        C * Real.exp (-c * l1dist d (origin d) z) := by
  rcases (phiIsing_nonneg d hbeta T).eq_or_lt with hzero | hpos
  · exact plusCorr_exponential_of_phi_eq_zero beta hbeta T ho hzero.symm
  · exact plusCorr_exponential_of_phi_lt_one beta hbeta T ho hpos hphi


theorem plusCorr_absorb_exponential_prefactor
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hsum : Summable (plusCorr d beta (origin d)))
    (c₀ : ℝ) (hc₀ : 0 < c₀) (C : ℝ) (hC : 0 < C)
    (hdecay : ∀ z : Site d,
      plusCorr d beta (origin d) z ≤
        C * Real.exp (-c₀ * l1dist d (origin d) z)) :
    ∃ c > 0, ∀ z : Site d,
      plusCorr d beta (origin d) z ≤
        Real.exp (-c * l1dist d (origin d) z) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * Real.log C / c₀)
  let rate : Site d → ℝ := fun z =>
    if z = origin d then c₀ / 2
    else if plusCorr d beta (origin d) z = 0 then c₀ / 2
    else -Real.log (plusCorr d beta (origin d) z) /
      l1dist d (origin d) z
  have hrate : ∀ z : Site d, 0 < rate z := by
    intro z
    by_cases hz : z = origin d
    · simp [rate, hz, hc₀]
    by_cases hcorr : plusCorr d beta (origin d) z = 0
    · simp [rate, hz, hcorr, hc₀]
    have hcorr0 : 0 < plusCorr d beta (origin d) z :=
      lt_of_le_of_ne (plusCorr_nonneg beta hbeta _ _) (Ne.symm hcorr)
    have hcorr1 : plusCorr d beta (origin d) z < 1 :=
      plusCorr_lt_one_of_summable beta hbeta hsum hz
    have hdist : 0 < l1dist d (origin d) z :=
      Nat.pos_of_ne_zero (fun h => hz (l1dist_origin_eq_zero_iff z |>.mp h))
    simp only [rate, if_neg hz, if_neg hcorr]
    exact div_pos (neg_pos.mpr (Real.log_neg hcorr0 hcorr1)) (by exact_mod_cast hdist)
  have horigin : origin d ∈ Ising.boxFinset d N :=
    mem_boxFinset_of_l1dist_origin_le N (origin d) (by simp)
  let cbox := (Ising.boxFinset d N).inf' ⟨origin d, horigin⟩ rate
  have hcbox : 0 < cbox := by
    rw [Finset.lt_inf'_iff]
    intro z _
    exact hrate z
  let c := min (c₀ / 2) cbox
  have hc : 0 < c := lt_min (half_pos hc₀) hcbox
  refine ⟨c, hc, ?_⟩
  intro z
  let r := l1dist d (origin d) z
  by_cases hr0 : r = 0
  · have hz : z = origin d := l1dist_origin_eq_zero_iff z |>.mp hr0
    subst z
    simpa [r] using plusCorr_le_one beta (origin d) (origin d)
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
  by_cases hrN : r ≤ N
  · have hzmem : z ∈ Ising.boxFinset d N :=
      mem_boxFinset_of_l1dist_origin_le N z hrN
    have hz : z ≠ origin d := fun h => hr0 (by simpa [r, h])
    have hcrate : c ≤ rate z :=
      (min_le_right (c₀ / 2) cbox).trans (Finset.inf'_le rate hzmem)
    by_cases hcorr : plusCorr d beta (origin d) z = 0
    · rw [hcorr]
      positivity
    have hcorr0 : 0 < plusCorr d beta (origin d) z :=
      lt_of_le_of_ne (plusCorr_nonneg beta hbeta _ _) (Ne.symm hcorr)
    have hquot : c ≤ -Real.log (plusCorr d beta (origin d) z) / (r : ℝ) := by
      simpa only [rate, if_neg hz, if_neg hcorr, r] using hcrate
    have hlog : Real.log (plusCorr d beta (origin d) z) ≤ -c * (r : ℝ) := by
      have hmul := (le_div_iff₀ (by exact_mod_cast hrpos : (0 : ℝ) < r)).mp hquot
      linarith
    rw [← Real.exp_log hcorr0]
    exact Real.exp_le_exp.mpr hlog
  · have hNr : (N : ℝ) < (r : ℝ) := by exact_mod_cast Nat.lt_of_not_ge hrN
    have hNmul : 2 * Real.log C < (N : ℝ) * c₀ :=
      (div_lt_iff₀ hc₀).mp hN
    have hlogC : Real.log C < (c₀ / 2) * (r : ℝ) := by
      nlinarith
    calc
      plusCorr d beta (origin d) z ≤ C * Real.exp (-c₀ * (r : ℝ)) := by
        simpa only [r] using hdecay z
      _ = Real.exp (Real.log C) * Real.exp (-c₀ * (r : ℝ)) := by
        rw [Real.exp_log hC]
      _ = Real.exp (Real.log C + -c₀ * (r : ℝ)) :=
        (Real.exp_add _ _).symm
      _ = Real.exp (Real.log C - c₀ * (r : ℝ)) := by ring
      _ ≤ Real.exp (-(c₀ / 2) * (r : ℝ)) :=
        Real.exp_le_exp.mpr (by linarith)
      _ ≤ Real.exp (-c * (r : ℝ)) := by
        apply Real.exp_le_exp.mpr
        have hca : c ≤ c₀ / 2 := min_le_left _ _
        nlinarith


theorem exponential_decay_with_prefactor_of_lt_tildeBetaCIsing
    {beta : ℝ} (hbeta : 0 ≤ beta) (hlt : beta < tildeBetaCIsing d) :
    ∃ c > 0, ∃ C > 0, ∀ z : Site d,
      plusCorr d beta (origin d) z ≤
        C * Real.exp (-c * l1dist d (origin d) z) := by
  obtain ⟨T, ho, hphi⟩ :=
    exists_phiIsing_witness_of_lt_tildeBetaCIsing hbeta hlt
  exact plusCorr_exponential_of_witness beta hbeta T ho hphi


theorem exponential_decay_of_lt_tildeBetaCIsing
    {beta : ℝ} (hbeta : 0 ≤ beta) (hlt : beta < tildeBetaCIsing d) :
    ∃ c > 0, ∀ z : Site d,
      plusCorr d beta (origin d) z ≤
        Real.exp (-c * l1dist d (origin d) z) := by
  obtain ⟨c₀, hc₀, C, hC, hdecay⟩ :=
    exponential_decay_with_prefactor_of_lt_tildeBetaCIsing
      (d := d) hbeta hlt
  obtain ⟨_T, _ho, _hphi, hsum⟩ :=
    finite_susceptibility_of_lt_tildeBetaCIsing (d := d) hbeta hlt
  exact plusCorr_absorb_exponential_prefactor beta hbeta hsum
    c₀ hc₀ C hC hdecay

end Sharpness
end StatMech
