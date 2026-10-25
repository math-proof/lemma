/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianPhysicalCumulants.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianWeightedMomentBridge.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianPhysicalCumulants
open Filter Finset Topology
open scoped BigOperators


namespace StatMech.FrontierA

noncomputable section

@[simp] theorem scalarCumulantsOfMoments_zero (moments : Nat -> Real) :
    scalarCumulantsOfMoments moments 0 = 0 := by
  rw [scalarCumulantsOfMoments]

theorem scalarCumulantsOfMoments_succ (moments : Nat -> Real) (n : Nat) :
    scalarCumulantsOfMoments moments (n + 1) = moments (n + 1) -
      ∑ k : Fin n, (n.choose k : Real) *
        scalarCumulantsOfMoments moments (k + 1) * moments (n - k) := by
  rw [scalarCumulantsOfMoments]


theorem hasScalarMomentCumulantRecurrence_cumulantsOfMoments
    (moments : Nat -> Nat -> Real)
    (hmomentZero : forall scale, moments scale 0 = 1) :
    HasScalarMomentCumulantRecurrence moments
      (fun scale => scalarCumulantsOfMoments (moments scale)) := by
  constructor
  · exact hmomentZero
  · intro scale order
    rw [Finset.sum_range_succ]
    have hprior :
        (∑ k ∈ Finset.range order,
          (order.choose k : Real) *
            scalarCumulantsOfMoments (moments scale) (k + 1) *
              moments scale (order - k)) =
          ∑ k : Fin order,
            (order.choose k : Real) *
              scalarCumulantsOfMoments (moments scale) (k + 1) *
                moments scale (order - k) := by
      simpa using (Fin.sum_univ_eq_sum_range (fun k : Nat =>
        (order.choose k : Real) *
          scalarCumulantsOfMoments (moments scale) (k + 1) *
            moments scale (order - k)) order).symm
    rw [hprior]
    simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self,
      hmomentZero, mul_one]
    rw [scalarCumulantsOfMoments_succ]
    ring


theorem scalarCumulantsOfMoments_eq_of_recurrence
    (moments cumulants : Nat -> Real)
    (hmomentZero : moments 0 = 1)
    (hcumulantZero : cumulants 0 = 0)
    (hrecurrence : forall order,
      moments (order + 1) =
        ∑ k ∈ Finset.range (order + 1),
          (order.choose k : Real) * cumulants (k + 1) *
            moments (order - k)) :
    forall order,
      scalarCumulantsOfMoments moments order = cumulants order := by
  intro order
  induction order using Nat.strong_induction_on with
  | h order ih =>
      cases order with
      | zero => simpa using hcumulantZero.symm
      | succ n =>
          rw [scalarCumulantsOfMoments_succ]
          have hrec := hrecurrence n
          rw [Finset.sum_range_succ] at hrec
          simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self,
            hmomentZero, mul_one] at hrec
          have hprior :
              (∑ k : Fin n, (n.choose k : Real) *
                scalarCumulantsOfMoments moments (k + 1) *
                  moments (n - k)) =
                ∑ k ∈ Finset.range n, (n.choose k : Real) *
                  cumulants (k + 1) * moments (n - k) := by
            rw [Fin.sum_univ_eq_sum_range (fun k : Nat =>
              (n.choose k : Real) *
                scalarCumulantsOfMoments moments (k + 1) *
                  moments (n - k)) n]
            apply Finset.sum_congr rfl
            intro k hk
            rw [ih (k + 1) (by simpa using Finset.mem_range.mp hk)]
          rw [hprior]
          linarith

@[simp] theorem scalarCumulantsOfMoments_one (moments : Nat -> Real) :
    scalarCumulantsOfMoments moments 1 = moments 1 := by
  rw [show 1 = 0 + 1 by omega, scalarCumulantsOfMoments_succ]
  simp

theorem scalarCumulantsOfMoments_two (moments : Nat -> Real) :
    scalarCumulantsOfMoments moments 2 =
      moments 2 - moments 1 ^ 2 := by
  rw [show 2 = 1 + 1 by omega, scalarCumulantsOfMoments_succ]
  rw [Fin.sum_univ_eq_sum_range (fun k : Nat =>
    ((1 : Nat).choose k : Real) * scalarCumulantsOfMoments moments (k + 1) *
      moments (1 - k)) 1]
  norm_num [Finset.sum_range_succ, scalarCumulantsOfMoments_one]
  ring

theorem scalarCumulantsOfMoments_three_of_centered
    (moments : Nat -> Real) (hone : moments 1 = 0)
    (hthree : moments 3 = 0) :
    scalarCumulantsOfMoments moments 3 = 0 := by
  rw [show 3 = 2 + 1 by omega, scalarCumulantsOfMoments_succ]
  rw [Fin.sum_univ_eq_sum_range (fun k : Nat =>
    ((2 : Nat).choose k : Real) * scalarCumulantsOfMoments moments (k + 1) *
      moments (2 - k)) 2]
  norm_num [Finset.sum_range_succ, scalarCumulantsOfMoments_one,
    scalarCumulantsOfMoments_two, hone, hthree]


theorem scalarCumulantsOfMoments_four_of_symmetric
    (moments : Nat -> Real) (hone : moments 1 = 0)
    (hthree : moments 3 = 0) :
    scalarCumulantsOfMoments moments 4 =
      scalarFourthCumulant (moments 4) (moments 2) := by
  rw [show 4 = 3 + 1 by omega, scalarCumulantsOfMoments_succ]
  rw [Fin.sum_univ_eq_sum_range (fun k : Nat =>
    ((3 : Nat).choose k : Real) * scalarCumulantsOfMoments moments (k + 1) *
      moments (3 - k)) 3]
  norm_num [Finset.sum_range_succ, scalarCumulantsOfMoments_one,
    scalarCumulantsOfMoments_two,
    scalarCumulantsOfMoments_three_of_centered moments hone hthree,
    hone, hthree, scalarFourthCumulant]
  ring


theorem scalarCumulantsOfMoments_odd
    (moments : Nat -> Real)
    (hmoments : forall order, Odd order -> moments order = 0) :
    forall order, Odd order -> scalarCumulantsOfMoments moments order = 0 := by
  intro order
  induction order using Nat.strong_induction_on with
  | h order ih =>
      intro horder
      cases order with
      | zero => exact (Nat.not_odd_zero horder).elim
      | succ n =>
          rw [scalarCumulantsOfMoments_succ, hmoments (n + 1) horder,
            zero_sub]
          apply neg_eq_zero.mpr
          apply Finset.sum_eq_zero
          intro k _
          rcases Nat.even_or_odd k.val with hkEven | hkOdd
          · have hkSuccOdd : Odd (k.val + 1) := hkEven.add_one
            rw [ih (k.val + 1) (by omega) hkSuccOdd]
            ring
          · have hnEven : Even n := by
              obtain ⟨q, hq⟩ := horder
              exact ⟨q, by omega⟩
            have hdiffOdd : Odd (n - k.val) :=
              Nat.Even.sub_odd (Nat.le_of_lt k.isLt) hnEven hkOdd
            rw [hmoments (n - k.val) hdiffOdd, mul_zero]


theorem scalarCumulantsOfMoments_scale
    (moments : Nat -> Real) (c : Real) :
    forall order,
      scalarCumulantsOfMoments (fun m => c ^ m * moments m) order =
        c ^ order * scalarCumulantsOfMoments moments order := by
  intro order
  induction order using Nat.strong_induction_on with
  | h order ih =>
      cases order with
      | zero => simp
      | succ n =>
          rw [scalarCumulantsOfMoments_succ,
            scalarCumulantsOfMoments_succ]
          have hsum :
              (∑ k : Fin n, (n.choose k : Real) *
                scalarCumulantsOfMoments
                  (fun m => c ^ m * moments m) (k + 1) *
                    (c ^ (n - k) * moments (n - k))) =
                c ^ (n + 1) *
                  ∑ k : Fin n, (n.choose k : Real) *
                    scalarCumulantsOfMoments moments (k + 1) *
                      moments (n - k) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            rw [ih (k.val + 1) (by omega)]
            have hexponent : k.val + 1 + (n - k.val) = n + 1 := by omega
            calc
              (n.choose k : Real) *
                    (c ^ (k.val + 1) *
                      scalarCumulantsOfMoments moments (k.val + 1)) *
                    (c ^ (n - k.val) * moments (n - k.val)) =
                  (c ^ (k.val + 1) * c ^ (n - k.val)) *
                    ((n.choose k : Real) *
                      scalarCumulantsOfMoments moments (k.val + 1) *
                        moments (n - k.val)) := by ring
              _ = c ^ (k.val + 1 + (n - k.val)) *
                    ((n.choose k : Real) *
                      scalarCumulantsOfMoments moments (k.val + 1) *
                        moments (n - k.val)) := by
                  exact congrArg
                    (fun x : Real => x *
                      ((n.choose k : Real) *
                        scalarCumulantsOfMoments moments (k.val + 1) *
                          moments (n - k.val)))
                    (pow_add c (k.val + 1) (n - k.val)).symm
              _ = _ := by rw [hexponent]
          rw [hsum]
          ring


theorem iteratedDeriv_zero_of_even_of_odd
    (F : Complex -> Complex) (heven : forall z, F (-z) = F z)
    (order : Nat) (horder : Odd order) :
    iteratedDeriv order F 0 = 0 := by
  have hfunction : (fun z => F (-z)) = F := by
    funext z
    exact heven z
  have hderiv := congrArg (fun f : Complex -> Complex =>
    iteratedDeriv order f 0) hfunction
  change iteratedDeriv order (fun z => F (-z)) 0 =
    iteratedDeriv order F 0 at hderiv
  rw [iteratedDeriv_comp_neg, neg_zero, horder.neg_one_pow,
    neg_one_smul] at hderiv
  exact CharZero.neg_eq_self_iff.mp hderiv

end
end StatMech.FrontierA
