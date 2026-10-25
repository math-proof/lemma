/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCriticalSummation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalCubeInfrared
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianIndependentDisentangling.Part3
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianCriticalSummation
open Filter Finset Set Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Lattice Percolation Sharpness StatMech.FrontierB

noncomputable section

variable {d : Nat}


theorem criticalFreePairKernel_nonneg
    (hd : 2 ≤ d) (x : Site d) :
    0 ≤ currentContinuityFreePairKernel d
      (IsingFK.betaC (magnetization d)) x := by
  by_cases hx : x = 0
  · simp [currentContinuityFreePairKernel, hx]
  · rw [currentContinuityFreePairKernel, if_neg hx]
    have hbeta : 0 < IsingFK.betaC (magnetization d) := by
      rw [isingFK_betaC_eq_tildeBetaCIsing hd]
      exact tildeBetaCIsing_pos hd
    rw [currentContinuityFreeTwoPoint_eq_freeInfiniteTwoPoint
      _ hbeta (by omega) (Percolation.origin d) x]
    · unfold StatMech.FK.infiniteTwoPointReal
      exact MeasureTheory.measureReal_nonneg
    · simpa [Percolation.origin] using Ne.symm hx


theorem criticalFreeBoxSusceptibility_nonneg
    (hd : 2 ≤ d) (R : Nat) :
    0 ≤ criticalFreeBoxSusceptibility d R := by
  unfold criticalFreeBoxSusceptibility
  exact Finset.sum_nonneg fun x _ => criticalFreePairKernel_nonneg hd x


theorem one_le_criticalFreeBoxSusceptibility
    (hd : 2 ≤ d) (R : Nat) :
    1 ≤ criticalFreeBoxSusceptibility d R := by
  rw [criticalFreeBoxSusceptibility]
  have hzero : (0 : Site d) ∈ boxSV_boxF d R := by
    rw [boxSV_mem_boxF]
    intro i
    simp
  have hterm := Finset.single_le_sum
    (s := boxSV_boxF d R)
    (f := fun x => currentContinuityFreePairKernel d
      (IsingFK.betaC (magnetization d)) x)
    (fun x _ => criticalFreePairKernel_nonneg hd x) hzero
  simpa [currentContinuityFreePairKernel] using hterm

theorem boxSV_boxF_succ_disjoint (d R : Nat) :
    boxSV_boxF d (R + 1) =
      boxSV_boxF d R ∪ boxSV_vbF d (R + 1) := by
  classical
  ext x
  simp only [boxSV_vbF, Finset.mem_union, Finset.mem_sdiff,
    Nat.add_sub_cancel]
  constructor
  · intro hx
    by_cases hinner : x ∈ boxSV_boxF d R
    · exact Or.inl hinner
    · exact Or.inr ⟨hx, hinner⟩
  · rintro (hx | ⟨hx, _⟩)
    · exact boxSV_boxF_subset d (Nat.le_succ R) hx
    · exact hx

theorem boxSV_boxF_disjoint_vbF_succ (d R : Nat) :
    Disjoint (boxSV_boxF d R) (boxSV_vbF d (R + 1)) := by
  classical
  rw [Finset.disjoint_left]
  intro x hx hboundary
  exact (Finset.mem_sdiff.mp hboundary).2 hx


theorem sum_boxSV_boxF_eq_sum_shells
    (f : Site d → Real) (R : Nat) :
    ∑ x ∈ boxSV_boxF d R, f x =
      f 0 + ∑ r ∈ Finset.range R,
        ∑ x ∈ boxSV_vbF d (r + 1), f x := by
  induction R with
  | zero =>
      have hbox : boxSV_boxF d 0 = {0} := by
        classical
        apply Finset.coe_injective
        rw [boxSV_coe_boxF]
        ext x
        simp only [Finset.coe_singleton, Set.mem_singleton_iff]
        rw [mem_box]
        constructor
        · intro hx
          funext i
          change x i = 0
          exact Int.natAbs_eq_zero.mp (Nat.le_zero.mp (hx i))
        · intro hx
          subst x
          intro i
          simp
      simp [hbox]
  | succ R ih =>
      rw [boxSV_boxF_succ_disjoint,
        Finset.sum_union (boxSV_boxF_disjoint_vbF_succ d R), ih,
        Finset.sum_range_succ]
      ring


theorem exists_criticalFreeBoxSusceptibility_le_quadratic
    (hd : 2 < d) :
    ∃ A : Real, 0 < A ∧ ∀ R : Nat,
      criticalFreeBoxSusceptibility d R ≤ A * (R + 1 : Real) ^ 2 := by
  obtain ⟨C, hC, hshell⟩ := exists_criticalFreeTwoPoint_shell_le_power
    (d := d) hd
  let r0 : Nat := 2 * d
  let A : Real :=
    1 + r0 * ((boxSV_boxF d r0).card : Real) +
      2 * d * 3 ^ (d - 1) * C
  have hA : 0 < A := by
    dsimp [A]
    positivity
  refine ⟨A, hA, ?_⟩
  intro R
  rw [criticalFreeBoxSusceptibility,
    sum_boxSV_boxF_eq_sum_shells]
  let f : Site d → Real := fun x =>
    currentContinuityFreePairKernel d
      (IsingFK.betaC (magnetization d)) x
  let S := (Finset.range R).filter (fun r => r + 1 < r0)
  let L := (Finset.range R).filter (fun r => r0 ≤ r + 1)
  have hsmall :
      ∑ r ∈ S, ∑ x ∈ boxSV_vbF d (r + 1), f x ≤
        (r0 : Real) * ((boxSV_boxF d r0).card : Real) := by
    have hterm (r : Nat) (hr : r ∈ S) :
        ∑ x ∈ boxSV_vbF d (r + 1), f x ≤
          ((boxSV_boxF d r0).card : Real) := by
      have hr0 : r + 1 ≤ r0 := by
        have := (Finset.mem_filter.mp hr).2
        omega
      calc
        ∑ x ∈ boxSV_vbF d (r + 1), f x ≤
            ∑ _x ∈ boxSV_vbF d (r + 1), (1 : Real) := by
          apply Finset.sum_le_sum
          intro x hx
          dsimp [f]
          by_cases hx0 : x = 0
          · simp [currentContinuityFreePairKernel, hx0]
          · rw [currentContinuityFreePairKernel, if_neg hx0]
            have hbeta : 0 < IsingFK.betaC (magnetization d) := by
              rw [isingFK_betaC_eq_tildeBetaCIsing (by omega : 2 ≤ d)]
              exact tildeBetaCIsing_pos (by omega)
            rw [currentContinuityFreeTwoPoint_eq_freeInfiniteTwoPoint
              _ hbeta (by omega) (Percolation.origin d) x]
            · unfold StatMech.FK.infiniteTwoPointReal
              exact MeasureTheory.measureReal_le_one
            · simpa [Percolation.origin] using Ne.symm hx0
        _ = ((boxSV_vbF d (r + 1)).card : Real) := by simp
        _ ≤ ((boxSV_boxF d r0).card : Real) := by
          exact_mod_cast Finset.card_le_card (fun x hx =>
            boxSV_boxF_subset d hr0 (Finset.mem_sdiff.mp hx).1)
    calc
      _ ≤ ∑ _r ∈ S, ((boxSV_boxF d r0).card : Real) := by
        apply Finset.sum_le_sum
        intro r hr
        exact hterm r hr
      _ = (S.card : Real) * ((boxSV_boxF d r0).card : Real) := by
        simp [nsmul_eq_mul]
      _ ≤ (r0 : Real) * ((boxSV_boxF d r0).card : Real) := by
        gcongr
        have hcardS : S.card ≤ r0 :=
          (Finset.card_le_card (show S ⊆ Finset.range r0 by
          intro r hr
          rw [Finset.mem_range]
          have := (Finset.mem_filter.mp hr).2
          omega)).trans_eq (Finset.card_range r0)
        exact_mod_cast hcardS
  have hlargeTerm (r : Nat) (hr : r ∈ L) :
      ∑ x ∈ boxSV_vbF d (r + 1), f x ≤
        (2 * d * 3 ^ (d - 1) * C) * (r + 1 : Real) := by
    let s := r + 1
    have hs0 : 1 ≤ s := by omega
    have hsr0 : r0 ≤ s := (Finset.mem_filter.mp hr).2
    have hpowPos : 0 < (s : Real) ^ (d - 2) := by positivity
    have hpoint (x : Site d) (hx : x ∈ boxSV_vbF d s) :
        f x ≤ C / (s : Real) ^ (d - 2) := by
      have hx0 : x ≠ 0 := by
        intro h
        subst x
        have hnot := (Finset.mem_sdiff.mp hx).2
        apply hnot
        rw [boxSV_mem_boxF]
        intro i
        simp
      dsimp [f]
      rw [currentContinuityFreePairKernel, if_neg hx0]
      exact hshell s (by simpa [r0] using hsr0) x hx
    have hcard := integerMomentumShell_card_le d s hs0
    have hthree : 2 * (s : Real) + 1 ≤ 3 * s := by
      have hsR : (1 : Real) ≤ s := by exact_mod_cast hs0
      linarith
    have hcard' : ((boxSV_vbF d s).card : Real) ≤
        2 * d * 3 ^ (d - 1) * (s : Real) ^ (d - 1) := by
      calc
        ((boxSV_vbF d s).card : Real) ≤
            2 * d * (2 * (s : Real) + 1) ^ (d - 1) := hcard
        _ ≤ 2 * d * (3 * (s : Real)) ^ (d - 1) := by gcongr
        _ = 2 * d * 3 ^ (d - 1) * (s : Real) ^ (d - 1) := by
          rw [mul_pow]
          ring
    calc
      ∑ x ∈ boxSV_vbF d s, f x ≤
          ∑ _x ∈ boxSV_vbF d s,
            C / (s : Real) ^ (d - 2) := by
        exact Finset.sum_le_sum fun x hx => hpoint x hx
      _ = ((boxSV_vbF d s).card : Real) *
          (C / (s : Real) ^ (d - 2)) := by simp [nsmul_eq_mul]
      _ ≤ (2 * d * 3 ^ (d - 1) * (s : Real) ^ (d - 1)) *
          (C / (s : Real) ^ (d - 2)) := by
        gcongr
      _ = (2 * d * 3 ^ (d - 1) * C) * (s : Real) := by
        have he : d - 1 = (d - 2) + 1 := by omega
        rw [he, pow_add, pow_one]
        field_simp [ne_of_gt hpowPos]
        ring
      _ = (2 * d * 3 ^ (d - 1) * C) * (r + 1 : Real) := by
        simp [s]
  have hlarge :
      ∑ r ∈ L, ∑ x ∈ boxSV_vbF d (r + 1), f x ≤
        (2 * d * 3 ^ (d - 1) * C) * (R + 1 : Real) ^ 2 := by
    let K : Real := 2 * d * 3 ^ (d - 1) * C
    have hK : 0 ≤ K := by positivity
    calc
      _ ≤ ∑ _r ∈ L, K * (R + 1 : Real) := by
        apply Finset.sum_le_sum
        intro r hr
        calc
          ∑ x ∈ boxSV_vbF d (r + 1), f x ≤ K * (r + 1 : Real) :=
            hlargeTerm r hr
          _ ≤ K * (R + 1 : Real) := by
            gcongr
            exact_mod_cast (Nat.le_of_lt
              (Finset.mem_range.mp (Finset.mem_filter.mp hr).1))
      _ = (L.card : Real) * (K * (R + 1 : Real)) := by
        simp [nsmul_eq_mul]
      _ ≤ (R + 1 : Real) * (K * (R + 1 : Real)) := by
        gcongr
        exact_mod_cast (Finset.card_le_card (Finset.filter_subset _ _)).trans
          (by simp)
      _ = K * (R + 1 : Real) ^ 2 := by ring
  have hsplit :
      (∑ r ∈ Finset.range R, ∑ x ∈ boxSV_vbF d (r + 1), f x) =
        (∑ r ∈ S, ∑ x ∈ boxSV_vbF d (r + 1), f x) +
        ∑ r ∈ L, ∑ x ∈ boxSV_vbF d (r + 1), f x := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := Finset.range R) (p := fun r => r + 1 < r0)]
    congr 2
    ext r
    simp [L]
  rw [hsplit]
  rw [show currentContinuityFreePairKernel d
      (IsingFK.betaC (magnetization d)) 0 = 1 by
    simp [currentContinuityFreePairKernel]]
  have hsq : (1 : Real) ≤ (R + 1 : Real) ^ 2 := by
    have hR : (0 : Real) ≤ R := Nat.cast_nonneg R
    nlinarith
  dsimp [A]
  nlinarith [mul_le_mul_of_nonneg_left hsq
    (show 0 ≤ (r0 : Real) * ((boxSV_boxF d r0).card : Real) by positivity)]


theorem criticalRenormalizedCoupling_tendsto_zero_of_treeDiagram
    (d : Nat) (hd : 4 < d) (coupling : Nat → Real)
    (htree : ∀ R,
      0 ≤ coupling R ∧
        coupling R ≤
          criticalFreeBoxSusceptibility d R ^ 2 / (R + 1 : Real) ^ d) :
    Tendsto coupling atTop (nhds 0) := by
  obtain ⟨A, hA, hchi⟩ :=
    exists_criticalFreeBoxSusceptibility_le_quadratic (d := d) (by omega)
  let radius : Nat → Real := fun R => (R + 1 : Nat)
  have hradius : Tendsto radius atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hpower : Tendsto (fun R => radius R ^ (d - 4)) atTop atTop := by
    apply Filter.tendsto_atTop_mono (fun R => ?_) hradius
    have hradiusOne : 1 ≤ radius R := by
      dsimp [radius]
      norm_num
    simpa only [pow_one] using
      pow_le_pow_right₀ hradiusOne (show 1 ≤ d - 4 by omega)
  have henvelope : Tendsto
      (fun R => A ^ 2 / radius R ^ (d - 4)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hpower
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun R => (htree R).1) _ henvelope
  filter_upwards with R
  have hradiusPos : 0 < radius R := by
    dsimp [radius]
    positivity
  have hchiNonneg : 0 ≤ criticalFreeBoxSusceptibility d R :=
    criticalFreeBoxSusceptibility_nonneg (d := d) (by omega) R
  have hchiSq : criticalFreeBoxSusceptibility d R ^ 2 ≤
      (A * radius R ^ 2) ^ 2 := by
    exact (sq_le_sq₀ hchiNonneg (by positivity)).2
      (by simpa [radius] using hchi R)
  calc
    coupling R ≤
        criticalFreeBoxSusceptibility d R ^ 2 / radius R ^ d := by
      simpa [radius] using (htree R).2
    _ ≤ (A * radius R ^ 2) ^ 2 / radius R ^ d := by
      exact div_le_div_of_nonneg_right hchiSq (pow_nonneg hradiusPos.le d)
    _ = A ^ 2 / radius R ^ (d - 4) := by
      have hd' : d = (d - 4) + 4 := by omega
      rw [hd', pow_add]
      field_simp
      congr 3
      omega

end
end StatMech.FrontierA
