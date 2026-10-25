/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ActiveInfluence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.BeffaraDC.ActiveRussoHamming
import Theorem.StatisticalMechanics.Code.FK.ComparisonHolley.Part3
import Def.StatisticalMechanics.Code.BeffaraDC.ActiveInfluence
open scoped BigOperators


namespace StatMech.BeffaraDC

open Finset

open StatMech.FK

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem activeInfluence_nonneg {p q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 1 ≤ q) (A : Set (ConfigSpace G.edgeSet)) (hA : IsIncreasing A)
    (e : G.edgeSet) : 0 ≤ activeInfluence G p q A e := by
  have hcov := active_fkg_cov G hp hp1 hq hA.indicator_monotone
    (OSSS.Lindeberg.coord_mono e)
  unfold activeInfluence activeCov at *
  have hm0 : 0 < openMarginal (activeProb G (fun _ => p) q) e := by
    have hr := active_reducedDensity_le_openMarginal G hp hp1 hq e
    exact lt_of_lt_of_le (reducedDensity_mem_Ioo hp hp1 hq).1 hr
  have hm1 : openMarginal (activeProb G (fun _ => p) q) e < 1 :=
    (active_openMarginal_le_param G (fun _ => hp) (fun _ => hp1) hq e).trans_lt hp1
  exact div_nonneg (by linarith) (mul_nonneg hm0.le (by linarith))

theorem activeCov_eq_marginal_mul_influence {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (A : Set (ConfigSpace G.edgeSet)) (e : G.edgeSet) :
    activeCov G (fun _ => p) q (A.indicator fun _ => (1 : ℝ))
        (OSSS.Lindeberg.coord e) =
      openMarginal (activeProb G (fun _ => p) q) e *
        (1 - openMarginal (activeProb G (fun _ => p) q) e) *
          activeInfluence G p q A e := by
  have hm0 : 0 < openMarginal (activeProb G (fun _ => p) q) e := by
    exact lt_of_lt_of_le (reducedDensity_mem_Ioo hp hp1 hq).1
      (active_reducedDensity_le_openMarginal G hp hp1 hq e)
  have hm1 : openMarginal (activeProb G (fun _ => p) q) e < 1 :=
    (active_openMarginal_le_param G (fun _ => hp) (fun _ => hp1) hq e).trans_lt hp1
  unfold activeInfluence
  field_simp [hm0.ne', (sub_pos.mpr hm1).ne']


theorem active_deriv_ge_total_influence {p q ε : ℝ} (hε : 0 < ε)
    (hp0 : ε ≤ p) (hp1 : p ≤ 1 - ε) (hq : 1 ≤ q)
    (A : Set (ConfigSpace G.edgeSet)) (hA : IsIncreasing A) :
    (ε ^ 2 / q) * (∑ e : G.edgeSet, activeInfluence G p q A e) ≤
      deriv (fun x => activeProbOf G (fun _ => x) q A) p := by
  have hp : 0 < p := hε.trans_le hp0
  have hp' : p < 1 := by linarith
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hden : 0 < p + q * (1 - p) := add_pos hp (mul_pos hq0 (by linarith))
  have hdenle : p + q * (1 - p) ≤ q := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hq) hp.le]
  have hred : ε / q ≤ reducedDensity p q := by
    rw [reducedDensity, div_le_div_iff₀ hq0 hden]
    exact mul_le_mul hp0 hdenle hden.le hp.le
  have hterm : ∀ e : G.edgeSet,
      ε ^ 2 / q * activeInfluence G p q A e ≤
        activeCov G (fun _ => p) q (A.indicator fun _ => (1 : ℝ))
          (OSSS.Lindeberg.coord e) := by
    intro e
    have hmlo : ε / q ≤ openMarginal (activeProb G (fun _ => p) q) e :=
      hred.trans (active_reducedDensity_le_openMarginal G hp hp' hq e)
    have hmhi := active_openMarginal_le_param G (fun _ => hp) (fun _ => hp') hq e
    have hclosed : ε ≤ 1 - openMarginal (activeProb G (fun _ => p) q) e := by
      linarith
    have hprod : ε ^ 2 / q ≤
        openMarginal (activeProb G (fun _ => p) q) e *
          (1 - openMarginal (activeProb G (fun _ => p) q) e) := by
      calc
        ε ^ 2 / q = (ε / q) * ε := by ring
        _ ≤ openMarginal (activeProb G (fun _ => p) q) e *
            (1 - openMarginal (activeProb G (fun _ => p) q) e) :=
          mul_le_mul hmlo hclosed hε.le
            ((div_nonneg hε.le hq0.le).trans hmlo)
    have hI := activeInfluence_nonneg G hp hp' hq A hA e
    rw [activeCov_eq_marginal_mul_influence G hp hp' hq A e]
    exact mul_le_mul_of_nonneg_right hprod hI
  have hsum : (ε ^ 2 / q) * (∑ e : G.edgeSet, activeInfluence G p q A e) ≤
      ∑ e : G.edgeSet, activeCov G (fun _ => p) q
        (A.indicator fun _ => (1 : ℝ)) (OSSS.Lindeberg.coord e) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun e _ => hterm e
  have hcovnonneg : 0 ≤ ∑ e : G.edgeSet, activeCov G (fun _ => p) q
      (A.indicator fun _ => (1 : ℝ)) (OSSS.Lindeberg.coord e) := by
    exact Finset.sum_nonneg fun e _ => by
      have h := active_fkg_cov G hp hp' hq hA.indicator_monotone
        (OSSS.Lindeberg.coord_mono e)
      unfold activeCov
      linarith
  rw [(hasDerivAt_activeProbOf_p G hp hp' hq0 A).deriv]
  refine hsum.trans ?_
  have hpden : 0 < p * (1 - p) := mul_pos hp (by linarith)
  rw [le_div_iff₀ hpden]
  have hpden_le : p * (1 - p) ≤ 1 := by nlinarith [mul_nonneg hp.le (by linarith)]
  nlinarith

end StatMech.BeffaraDC
