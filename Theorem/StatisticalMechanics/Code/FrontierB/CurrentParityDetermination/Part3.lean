/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentParityDetermination.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentConditionalPMF.Part7
import Def.StatisticalMechanics.Code.FrontierB.CurrentParityDetermination.Part3
open MeasureTheory
open scoped ENNReal BigOperators


namespace StatMech.FrontierB

theorem finiteParityKernel_eq_zero_of_ne {E : Type*} [DecidableEq E]
    (S : Finset E) (beta : ℝ) (odd : ↑S → Bool) (a : ↑S → ℕ)
    (hne : odd ≠ currentLocalParity a) :
    finiteParityKernel S beta odd a = 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  unfold finiteParityKernel
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  cases hodd : odd i
  · have hi' : false ≠ decide (Odd (a i)) := by
      simpa [currentLocalParity, hodd] using hi
    have hd : decide (Odd (a i)) = true :=
      Bool.eq_true_of_not_eq_false (Ne.symm hi')
    have hpar : Odd (a i) := of_decide_eq_true hd
    have heven : ¬ Even (a i) := Nat.not_even_iff_odd.mpr hpar
    simp [parityEdgeKernel, heven]
  · have hi' : true ≠ decide (Odd (a i)) := by
      simpa [currentLocalParity, hodd] using hi
    have hd : decide (Odd (a i)) = false :=
      Bool.eq_false_of_not_eq_true (Ne.symm hi')
    have hpar : ¬ Odd (a i) := of_decide_eq_false hd
    simp [parityEdgeKernel, hpar]

theorem finiteParityPMF_eq_zero_of_ne {E : Type*} [DecidableEq E]
    (S : Finset E) (beta : ℝ) (hbeta : 0 < beta)
    (odd : ↑S → Bool) (a : ↑S → ℕ)
    (hne : odd ≠ currentLocalParity a) :
    finiteParityPMF S beta hbeta odd a = 0 := by
  rw [finiteParityPMF_apply,
    finiteParityKernel_eq_zero_of_ne S beta odd a hne]
  simp

theorem bind_finiteParityPMF_apply {E : Type*} [DecidableEq E]
    (S : Finset E) (beta : ℝ) (hbeta : 0 < beta)
    (p : PMF (↑S → Bool)) (a : ↑S → ℕ) :
    p.bind (finiteParityPMF S beta hbeta) a =
      p (currentLocalParity a) *
        finiteParityPMF S beta hbeta (currentLocalParity a) a := by
  rw [PMF.bind_apply, tsum_eq_single (currentLocalParity a)]
  intro odd hodd
  rw [finiteParityPMF_eq_zero_of_ne S beta hbeta odd a hodd]
  simp

end StatMech.FrontierB
