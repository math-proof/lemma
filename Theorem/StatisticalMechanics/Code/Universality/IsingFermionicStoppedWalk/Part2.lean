/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRegularity.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicStoppedWalk.Part3


namespace StatMech.Universality

open Finset

noncomputable section

@[simp] theorem isingLeapfrogStoppedMean_zero (R : Nat)
    (f : IsingLeapfrogBox R → Complex) (p : IsingLeapfrogBox R) :
    isingLeapfrogStoppedMean R 0 f p = f p := by
  classical
  unfold isingLeapfrogStoppedMean isingLeapfrogStoppedKernel
  have hcast (q : IsingLeapfrogBox R) :
      ((if p = q then 1 else 0 : Real) : Complex) =
        if p = q then 1 else 0 := by
    split_ifs <;> simp_all
  simp_rw [hcast]
  simp

theorem isingLeapfrogStoppedMean_succ (R t : Nat)
    (f : IsingLeapfrogBox R → Complex) (p : IsingLeapfrogBox R) :
    isingLeapfrogStoppedMean R (t + 1) f p =
      if hp : isingLeapfrogBoxBoundary R p then
        isingLeapfrogStoppedMean R t f p
      else
        (isingLeapfrogStoppedMean R t f (isingLeapfrogSW R p) +
          isingLeapfrogStoppedMean R t f (isingLeapfrogSE R p hp) +
          isingLeapfrogStoppedMean R t f (isingLeapfrogNW R p hp) +
          isingLeapfrogStoppedMean R t f (isingLeapfrogNE R p hp)) / 4 := by
  classical
  unfold isingLeapfrogStoppedMean
  by_cases hp : isingLeapfrogBoxBoundary R p
  · simp [isingLeapfrogStoppedKernel, hp]
  · simp only [isingLeapfrogStoppedKernel, dif_neg hp]
    push_cast
    have hdist (a b c d z : Complex) :
        ((a + b + c + d) / 4) * z =
          (a * z + b * z + c * z + d * z) / 4 := by ring
    simp_rw [hdist]
    rw [← Finset.sum_div]
    repeat' rw [Finset.sum_add_distrib]


theorem isingLeapfrogStoppedKernel_nonneg (R t : Nat)
    (p q : IsingLeapfrogBox R) :
    0 ≤ isingLeapfrogStoppedKernel R t p q := by
  induction t generalizing p with
  | zero =>
      unfold isingLeapfrogStoppedKernel
      split_ifs <;> norm_num
  | succ t ih =>
      simp only [isingLeapfrogStoppedKernel]
      split_ifs with hp
      · exact ih p
      · have hSW := ih (isingLeapfrogSW R p)
        have hSE := ih (isingLeapfrogSE R p hp)
        have hNW := ih (isingLeapfrogNW R p hp)
        have hNE := ih (isingLeapfrogNE R p hp)
        positivity


theorem isingLeapfrogStoppedKernel_sum_eq_one (R t : Nat)
    (p : IsingLeapfrogBox R) :
    ∑ q, isingLeapfrogStoppedKernel R t p q = 1 := by
  induction t generalizing p with
  | zero =>
      unfold isingLeapfrogStoppedKernel
      simp
  | succ t ih =>
      simp only [isingLeapfrogStoppedKernel]
      split_ifs with hp
      · exact ih p
      · rw [← Finset.sum_div]
        repeat' rw [Finset.sum_add_distrib]
        rw [ih, ih, ih, ih]
        norm_num

theorem isingLeapfrogStoppedKernel_le_one (R t : Nat)
    (p q : IsingLeapfrogBox R) :
    isingLeapfrogStoppedKernel R t p q ≤ 1 := by
  classical
  calc
    isingLeapfrogStoppedKernel R t p q ≤
        ∑ x, isingLeapfrogStoppedKernel R t p x := by
      exact Finset.single_le_sum
        (fun x _ ↦ isingLeapfrogStoppedKernel_nonneg R t p x)
        (Finset.mem_univ q)
    _ = 1 := isingLeapfrogStoppedKernel_sum_eq_one R t p


theorem isingLeapfrogStoppedKernel_add (R t s : Nat)
    (p q : IsingLeapfrogBox R) :
    isingLeapfrogStoppedKernel R (t + s) p q =
      ∑ r, isingLeapfrogStoppedKernel R t p r *
        isingLeapfrogStoppedKernel R s r q := by
  classical
  induction t generalizing p with
  | zero =>
      simp [isingLeapfrogStoppedKernel]
  | succ t ih =>
      rw [Nat.succ_add]
      simp only [isingLeapfrogStoppedKernel]
      by_cases hp : isingLeapfrogBoxBoundary R p
      · simp only [dif_pos hp]
        exact ih p
      · simp only [dif_neg hp]
        rw [ih, ih, ih, ih]
        repeat' rw [← Finset.sum_add_distrib]
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro r hr
        ring


theorem isingLeapfrogStoppedKernel_l1_add_le
    (R t t' s : Nat) (p p' : IsingLeapfrogBox R) :
    (∑ q, |isingLeapfrogStoppedKernel R (t + s) p q -
        isingLeapfrogStoppedKernel R (t' + s) p' q|) ≤
      ∑ r, |isingLeapfrogStoppedKernel R t p r -
        isingLeapfrogStoppedKernel R t' p' r| := by
  classical
  simp_rw [isingLeapfrogStoppedKernel_add R t s p,
    isingLeapfrogStoppedKernel_add R t' s p']
  simp_rw [← Finset.sum_sub_distrib, ← sub_mul]
  calc
    _ ≤ ∑ q, ∑ r, |isingLeapfrogStoppedKernel R t p r -
          isingLeapfrogStoppedKernel R t' p' r| *
        isingLeapfrogStoppedKernel R s r q := by
      apply Finset.sum_le_sum
      intro q hq
      refine le_trans (Finset.abs_sum_le_sum_abs _ Finset.univ) ?_
      apply Finset.sum_le_sum
      intro r hr
      rw [abs_mul, abs_of_nonneg
        (isingLeapfrogStoppedKernel_nonneg R s r q)]
    _ = ∑ r, ∑ q, |isingLeapfrogStoppedKernel R t p r -
          isingLeapfrogStoppedKernel R t' p' r| *
        isingLeapfrogStoppedKernel R s r q := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [← Finset.mul_sum, isingLeapfrogStoppedKernel_sum_eq_one,
        mul_one]


theorem isingLeapfrogStoppedKernel_of_boundary (R t : Nat)
    (p q : IsingLeapfrogBox R) (hp : isingLeapfrogBoxBoundary R p) :
    isingLeapfrogStoppedKernel R t p q = if p = q then 1 else 0 := by
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [isingLeapfrogStoppedKernel, dif_pos hp]
      exact ih


theorem isingLeapfrogStoppedKernel_boundary_mono (R t : Nat)
    (p q : IsingLeapfrogBox R) (hq : isingLeapfrogBoxBoundary R q) :
    isingLeapfrogStoppedKernel R t p q ≤
      isingLeapfrogStoppedKernel R (t + 1) p q := by
  induction t generalizing p with
  | zero =>
      by_cases hp : isingLeapfrogBoxBoundary R p
      · rw [isingLeapfrogStoppedKernel_of_boundary R 0 p q hp,
          isingLeapfrogStoppedKernel_of_boundary R 1 p q hp]
      · have hpq : p ≠ q := fun hpq ↦ hp (hpq ▸ hq)
        rw [isingLeapfrogStoppedKernel_succ R 0 p q]
        simp only [isingLeapfrogStoppedKernel, hpq, if_false, dif_neg hp]
        have hSW := isingLeapfrogStoppedKernel_nonneg R 0
          (isingLeapfrogSW R p) q
        have hSE := isingLeapfrogStoppedKernel_nonneg R 0
          (isingLeapfrogSE R p hp) q
        have hNW := isingLeapfrogStoppedKernel_nonneg R 0
          (isingLeapfrogNW R p hp) q
        have hNE := isingLeapfrogStoppedKernel_nonneg R 0
          (isingLeapfrogNE R p hp) q
        positivity
  | succ t ih =>
      rw [isingLeapfrogStoppedKernel_succ R t p q,
        isingLeapfrogStoppedKernel_succ R (t + 1) p q]
      by_cases hp : isingLeapfrogBoxBoundary R p
      · simp only [dif_pos hp]
        exact ih p
      · simp only [dif_neg hp]
        have hSW := ih (isingLeapfrogSW R p)
        have hSE := ih (isingLeapfrogSE R p hp)
        have hNW := ih (isingLeapfrogNW R p hp)
        have hNE := ih (isingLeapfrogNE R p hp)
        linarith


end
end StatMech.Universality
