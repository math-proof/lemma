/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoInfluence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.Russo
import Def.StatisticalMechanics.Code.BeffaraDC.RussoInfluence.Part2


namespace StatMech

namespace BeffaraDC

open ConfigSpace Function Finset

variable {E : Type*} [Fintype E] [DecidableEq E]


lemma influence_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A : Set (ConfigSpace E)) (e : E) : 0 ≤ influence p A e :=
  pivotalProb_nonneg hp0 hp1 A e


theorem cov_ge_influence {p ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1/2)
    (hpl : ε ≤ p) (hpr : p ≤ 1 - ε)
    (A : Set (ConfigSpace E)) (hA : IsIncreasing A) (e : E) :
    ε * (1 - ε) * influence p A e
      ≤ prob p (A ∩ openEdge e) - prob p (openEdge e) * prob p A := by
  rw [cov_eq p A hA e]
  unfold influence
  have hp0 : 0 ≤ p := le_trans hε0.le hpl
  have hp1 : p ≤ 1 := by linarith
  have hpiv : 0 ≤ pivotalProb p A e := pivotalProb_nonneg hp0 hp1 A e
  have hfac : ε * (1 - ε) ≤ p * (1 - p) := by nlinarith [hε0, hpl, hpr]
  nlinarith [hpiv, hfac]


theorem deriv_ge_total_influence {p ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1/2)
    (hpl : ε ≤ p) (hpr : p ≤ 1 - ε)
    (A : Set (ConfigSpace E)) (hA : IsIncreasing A) :
    ε * (1 - ε) * ∑ e, influence p A e ≤ deriv (fun p => prob p A) p := by
  rw [deriv_prob_eq_sum_pivotalProb A hA p]
  have hp0 : 0 ≤ p := le_trans hε0.le hpl
  have hp1 : p ≤ 1 := by linarith
  unfold influence
  rw [Finset.mul_sum]
  calc ∑ e, ε * (1 - ε) * pivotalProb p A e
      ≤ ∑ e, p * (1 - p) * pivotalProb p A e := by
        refine Finset.sum_le_sum (fun e _ => ?_)
        have hfac : ε * (1 - ε) ≤ p * (1 - p) := by nlinarith [hε0, hpl, hpr]
        have hpiv := pivotalProb_nonneg hp0 hp1 A e
        nlinarith [hfac, hpiv]
    _ ≤ ∑ e, pivotalProb p A e := by
        refine Finset.sum_le_sum (fun e _ => ?_)
        have hpiv := pivotalProb_nonneg hp0 hp1 A e
        have hle1 : p * (1 - p) ≤ 1 := by nlinarith [hp0, hp1]
        nlinarith [hle1, hpiv]


theorem deriv_eq_total_influence (p : ℝ) (A : Set (ConfigSpace E)) (hA : IsIncreasing A) :
    deriv (fun p => prob p A) p = ∑ e, influence p A e := by
  rw [deriv_prob_eq_sum_pivotalProb A hA p]
  rfl

end BeffaraDC
end StatMech
