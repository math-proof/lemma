/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeGKS.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeElitzur.Part2
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeGKS
open scoped BigOperators symmDiff
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unnecessarySeqFocus false


namespace StatMech.FrontierA

noncomputable section

variable {E P : Type*} [Fintype E] [DecidableEq E]
  [Fintype P] [DecidableEq P]

theorem gaugeAction_addPlaquetteCoupling
    (incidence : P -> Finset E) (K : P -> Real) (p : P) (delta : Real)
    (sigma : GaugeConfig E) :
    gaugeAction incidence (addGaugePlaquetteCoupling K p delta) sigma =
      gaugeAction incidence K sigma + delta * plaquetteSpin incidence sigma p := by
  unfold gaugeAction addGaugePlaquetteCoupling
  calc
    (∑ q : P, (if q = p then K q + delta else K q) *
        plaquetteSpin incidence sigma q) =
      ∑ q : P, (K q * plaquetteSpin incidence sigma q +
        if q = p then delta * plaquetteSpin incidence sigma q else 0) := by
        apply Finset.sum_congr rfl
        intro q _
        by_cases hqp : q = p <;> simp [hqp] <;> ring
    _ = (∑ q : P, K q * plaquetteSpin incidence sigma q) +
        ∑ q : P, if q = p then delta * plaquetteSpin incidence sigma q else 0 := by
      rw [Finset.sum_add_distrib]
    _ = _ := by simp

theorem gaugeWeight_addPlaquetteCoupling
    (incidence : P -> Finset E) (K : P -> Real) (p : P) (delta : Real)
    (sigma : GaugeConfig E) :
    gaugeWeight incidence (addGaugePlaquetteCoupling K p delta) sigma =
      gaugeWeight incidence K sigma *
        (Real.cosh delta + plaquetteSpin incidence sigma p * Real.sinh delta) := by
  unfold gaugeWeight
  rw [gaugeAction_addPlaquetteCoupling, Real.exp_add,
    StatMech.Ising.exp_mul_pm delta (plaquetteSpin incidence sigma p)
      (plaquetteSpin_eq_one_or_neg_one incidence sigma p)]


theorem gaugeWilsonNumerator_addPlaquetteCoupling
    (incidence : P -> Finset E) (K : P -> Real) (p : P) (delta : Real)
    (L : Finset E) :
    gaugeWilsonNumerator incidence (addGaugePlaquetteCoupling K p delta) L =
      Real.cosh delta * gaugeWilsonNumerator incidence K L +
        Real.sinh delta * gaugeWilsonNumerator incidence K (L ∆ incidence p) := by
  unfold gaugeWilsonNumerator
  simp_rw [gaugeWeight_addPlaquetteCoupling]
  calc
    (∑ sigma : GaugeConfig E, wilsonSpin L sigma *
        (gaugeWeight incidence K sigma *
          (Real.cosh delta + plaquetteSpin incidence sigma p * Real.sinh delta))) =
      ∑ sigma : GaugeConfig E,
        (Real.cosh delta * (wilsonSpin L sigma * gaugeWeight incidence K sigma) +
          Real.sinh delta *
            (wilsonSpin (L ∆ incidence p) sigma * gaugeWeight incidence K sigma)) := by
        apply Finset.sum_congr rfl
        intro sigma _
        rw [← wilsonSpin_mul_self L (incidence p) sigma]
        rw [show plaquetteSpin incidence sigma p =
          wilsonSpin (incidence p) sigma by rfl]
        ring
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]


theorem gaugePartition_addPlaquetteCoupling
    (incidence : P -> Finset E) (K : P -> Real) (p : P) (delta : Real) :
    gaugePartition incidence (addGaugePlaquetteCoupling K p delta) =
      Real.cosh delta * gaugePartition incidence K +
        Real.sinh delta * gaugeWilsonNumerator incidence K (incidence p) := by
  unfold gaugePartition gaugeWilsonNumerator
  simp_rw [gaugeWeight_addPlaquetteCoupling]
  calc
    (∑ sigma : GaugeConfig E, gaugeWeight incidence K sigma *
        (Real.cosh delta + plaquetteSpin incidence sigma p * Real.sinh delta)) =
      ∑ sigma : GaugeConfig E,
        (Real.cosh delta * gaugeWeight incidence K sigma +
          Real.sinh delta *
            (wilsonSpin (incidence p) sigma * gaugeWeight incidence K sigma)) := by
        apply Finset.sum_congr rfl
        intro sigma _
        rw [show plaquetteSpin incidence sigma p =
          wilsonSpin (incidence p) sigma by rfl]
        ring
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]


theorem gaugeWilsonExpectation_le_addPlaquetteCoupling
    (incidence : P -> Finset E) (K : P -> Real)
    (hK : forall q, 0 <= K q) (p : P) {delta : Real} (hdelta : 0 <= delta)
    (L : Finset E) :
    gaugeWilsonExpectation incidence K L <=
      gaugeWilsonExpectation incidence (addGaugePlaquetteCoupling K p delta) L := by
  let Z := gaugePartition incidence K
  let N := gaugeWilsonNumerator incidence K L
  let Pn := gaugeWilsonNumerator incidence K (incidence p)
  let NP := gaugeWilsonNumerator incidence K (L ∆ incidence p)
  have hZ : 0 < Z := gaugePartition_pos incidence K
  have hZ' : 0 < gaugePartition incidence (addGaugePlaquetteCoupling K p delta) :=
    gaugePartition_pos incidence (addGaugePlaquetteCoupling K p delta)
  have hgks : N * Pn <= NP * Z :=
    gaugeWilsonNumerator_mul_le incidence K hK L (incidence p)
  have hsinh : 0 <= Real.sinh delta := Real.sinh_nonneg_iff.mpr hdelta
  unfold gaugeWilsonExpectation
  rw [gaugeWilsonNumerator_addPlaquetteCoupling,
    gaugePartition_addPlaquetteCoupling]
  change N / Z <=
    (Real.cosh delta * N + Real.sinh delta * NP) /
      (Real.cosh delta * Z + Real.sinh delta * Pn)
  have hden : 0 < Real.cosh delta * Z + Real.sinh delta * Pn := by
    rw [← gaugePartition_addPlaquetteCoupling incidence K p delta]
    exact hZ'
  rw [div_le_div_iff₀ hZ hden]
  nlinarith [mul_le_mul_of_nonneg_left hgks hsinh]


theorem gaugeWilsonExpectation_mono_coupling
    (incidence : P -> Finset E) (K K' : P -> Real)
    (hK : forall p, 0 <= K p) (hKK' : forall p, K p <= K' p)
    (L : Finset E) :
    gaugeWilsonExpectation incidence K L <=
      gaugeWilsonExpectation incidence K' L := by
  let replaceOn (S : Finset P) : P -> Real :=
    fun p => if p ∈ S then K' p else K p
  have hstep : forall S : Finset P,
      gaugeWilsonExpectation incidence K L <=
        gaugeWilsonExpectation incidence (replaceOn S) L := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp [replaceOn]
    | @insert p S hp ih =>
        have hcurrent : forall q, 0 <= replaceOn S q := by
          intro q
          by_cases hq : q ∈ S
          · simpa [replaceOn, hq] using le_trans (hK q) (hKK' q)
          · simpa [replaceOn, hq] using hK q
        have hdelta : 0 <= K' p - K p := sub_nonneg.mpr (hKK' p)
        have hreplace : replaceOn (insert p S) =
            addGaugePlaquetteCoupling (replaceOn S) p (K' p - K p) := by
          funext q
          by_cases hqp : q = p
          · subst q
            simp [replaceOn, addGaugePlaquetteCoupling, hp]
          · simp [replaceOn, addGaugePlaquetteCoupling, hqp]
        rw [hreplace]
        exact ih.trans (gaugeWilsonExpectation_le_addPlaquetteCoupling
          incidence (replaceOn S) hcurrent p hdelta L)
  simpa [replaceOn] using hstep (Finset.univ : Finset P)

end
end StatMech.FrontierA
