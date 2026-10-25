/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeGKS.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeElitzur.Part2
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
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

omit [Fintype P] [DecidableEq P] in
@[simp] theorem gaugeEdgeSpin_xnor
    (sigma q : GaugeConfig E) (e : E) :
    gaugeEdgeSpin (StatMech.Ising.xnor sigma q) e =
      gaugeEdgeSpin sigma e * gaugeEdgeSpin q e := by
  exact StatMech.Ising.spin_xnor sigma q e

omit [Fintype P] [DecidableEq P] in
theorem plaquetteSpin_xnor
    (incidence : P -> Finset E) (sigma q : GaugeConfig E) (p : P) :
    plaquetteSpin incidence (StatMech.Ising.xnor sigma q) p =
      plaquetteSpin incidence sigma p * plaquetteSpin incidence q p := by
  unfold plaquetteSpin
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun e _ => gaugeEdgeSpin_xnor sigma q e)

omit [Fintype P] [DecidableEq P] in
theorem wilsonSpin_xnor (L : Finset E) (sigma q : GaugeConfig E) :
    wilsonSpin L (StatMech.Ising.xnor sigma q) =
      wilsonSpin L sigma * wilsonSpin L q := by
  unfold wilsonSpin
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun e _ => gaugeEdgeSpin_xnor sigma q e)

omit [Fintype P] [DecidableEq P] in
theorem wilsonSpin_mul_self (A B : Finset E) (sigma : GaugeConfig E) :
    wilsonSpin A sigma * wilsonSpin B sigma = wilsonSpin (A ∆ B) sigma := by
  simpa only [wilsonSpin, gaugeEdgeSpin] using
    StatMech.Ising.spinProd_mul_self A B sigma

omit [Fintype P] [DecidableEq P] in
theorem isSpinMonomial_plaquetteSpin (incidence : P -> Finset E) (p : P) :
    StatMech.Ising.IsSpinMonomial (fun sigma => plaquetteSpin incidence sigma p) := by
  simpa only [plaquetteSpin, gaugeEdgeSpin, StatMech.Ising.spinProd] using
    StatMech.Ising.isSpinMonomial_spinProd (incidence p)

omit [Fintype P] [DecidableEq P] in
theorem isSpinMonomial_wilsonSpin (L : Finset E) :
    StatMech.Ising.IsSpinMonomial (wilsonSpin L : GaugeConfig E -> Real) := by
  simpa only [wilsonSpin, gaugeEdgeSpin, StatMech.Ising.spinProd] using
    StatMech.Ising.isSpinMonomial_spinProd L

omit [Fintype E] [DecidableEq E] [Fintype P] [DecidableEq P] in
theorem one_add_plaquetteSpin_nonneg
    (incidence : P -> Finset E) (q : GaugeConfig E) (p : P) :
    0 <= 1 + plaquetteSpin incidence q p := by
  rcases plaquetteSpin_eq_one_or_neg_one incidence q p with h | h <;>
    rw [h] <;> norm_num

omit [Fintype P] [DecidableEq P] in
theorem one_sub_wilsonSpin_nonneg (L : Finset E) (q : GaugeConfig E) :
    0 <= 1 - wilsonSpin L q := by
  simpa only [wilsonSpin, gaugeEdgeSpin, StatMech.Ising.spinProd] using
    StatMech.Ising.one_sub_spinProd_nonneg L q


theorem gaugeWeight_mul_xnor
    (incidence : P -> Finset E) (K : P -> Real)
    (sigma q : GaugeConfig E) :
    gaugeWeight incidence K sigma *
        gaugeWeight incidence K (StatMech.Ising.xnor sigma q) =
      gaugeWeight incidence
        (fun p => K p * (1 + plaquetteSpin incidence q p)) sigma := by
  unfold gaugeWeight gaugeAction
  rw [← Real.exp_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  rw [plaquetteSpin_xnor]
  ring


theorem gauge_monomial_weight_sum_nonneg
    (incidence : P -> Finset E) (K : P -> Real)
    (hK : forall p, 0 <= K p)
    (obs : GaugeConfig E -> Real)
    (hobs : StatMech.Ising.IsSpinMonomial obs) :
    0 <= ∑ sigma : GaugeConfig E, obs sigma * gaugeWeight incidence K sigma := by
  have hkernel : 0 <= ∑ sigma : GaugeConfig E,
      obs sigma * ∏ p : P,
        (1 + Real.tanh (K p) * plaquetteSpin incidence sigma p) := by
    have h := StatMech.Ising.gks_kernel (Finset.univ : Finset P)
      (fun _ => (1 : Real)) (fun p => Real.tanh (K p))
      (fun _ _ => by norm_num)
      (fun p _ => by
        change 0 <= Real.tanh (K p)
        rw [Real.tanh_eq_sinh_div_cosh]
        exact div_nonneg (Real.sinh_nonneg_iff.mpr (hK p)) (Real.cosh_pos _).le)
      (fun p sigma => plaquetteSpin incidence sigma p)
      (fun p _ => isSpinMonomial_plaquetteSpin incidence p) obs hobs
    simpa only [Finset.mem_univ, Finset.prod_const, Nat.card_eq_fintype_card,
      one_pow, mul_comm] using h
  have hcosh : 0 <= ∏ p : P, Real.cosh (K p) :=
    Finset.prod_nonneg (fun p _ => (Real.cosh_pos (K p)).le)
  simp_rw [gaugeWeight_eq_highTempFactors incidence K]
  calc
    0 <= (∏ p : P, Real.cosh (K p)) *
        ∑ sigma : GaugeConfig E, obs sigma *
          ∏ p : P, (1 + Real.tanh (K p) * plaquetteSpin incidence sigma p) :=
      mul_nonneg hcosh hkernel
    _ = ∑ sigma : GaugeConfig E, obs sigma *
        ((∏ p : P, Real.cosh (K p)) *
          ∏ p : P, (1 + Real.tanh (K p) * plaquetteSpin incidence sigma p)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro sigma _
      ring


theorem gauge_inner_q_nonneg
    (incidence : P -> Finset E) (K : P -> Real)
    (hK : forall p, 0 <= K p) (A B : Finset E) (q : GaugeConfig E) :
    0 <= ∑ sigma : GaugeConfig E,
      (wilsonSpin (A ∆ B) sigma * gaugeWeight incidence K sigma *
          gaugeWeight incidence K (StatMech.Ising.xnor sigma q) -
        wilsonSpin A sigma * gaugeWeight incidence K sigma *
          (wilsonSpin B (StatMech.Ising.xnor sigma q) *
            gaugeWeight incidence K (StatMech.Ising.xnor sigma q))) := by
  have key : forall sigma : GaugeConfig E,
      (wilsonSpin (A ∆ B) sigma * gaugeWeight incidence K sigma *
          gaugeWeight incidence K (StatMech.Ising.xnor sigma q) -
        wilsonSpin A sigma * gaugeWeight incidence K sigma *
          (wilsonSpin B (StatMech.Ising.xnor sigma q) *
            gaugeWeight incidence K (StatMech.Ising.xnor sigma q))) =
      (1 - wilsonSpin B q) *
        ((wilsonSpin A sigma * wilsonSpin B sigma) *
          gaugeWeight incidence
            (fun p => K p * (1 + plaquetteSpin incidence q p)) sigma) := by
    intro sigma
    rw [← gaugeWeight_mul_xnor incidence K sigma q,
      wilsonSpin_xnor, ← wilsonSpin_mul_self]
    ring
  rw [Finset.sum_congr rfl (fun sigma _ => key sigma), ← Finset.mul_sum]
  apply mul_nonneg (one_sub_wilsonSpin_nonneg B q)
  apply gauge_monomial_weight_sum_nonneg
  · intro p
    exact mul_nonneg (hK p) (one_add_plaquetteSpin_nonneg incidence q p)
  · exact (isSpinMonomial_wilsonSpin A).mul (isSpinMonomial_wilsonSpin B)


theorem gaugeWilsonNumerator_mul_le
    (incidence : P -> Finset E) (K : P -> Real)
    (hK : forall p, 0 <= K p) (A B : Finset E) :
    gaugeWilsonNumerator incidence K A * gaugeWilsonNumerator incidence K B <=
      gaugeWilsonNumerator incidence K (A ∆ B) * gaugePartition incidence K := by
  unfold gaugeWilsonNumerator gaugePartition
  rw [← sub_nonneg, Finset.sum_mul_sum, Finset.sum_mul_sum]
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  rw [← Finset.sum_sub_distrib]
  rw [StatMech.Ising.sum_dbl_reindex (fun pair =>
    wilsonSpin (A ∆ B) pair.1 * gaugeWeight incidence K pair.1 *
        gaugeWeight incidence K pair.2 -
      wilsonSpin A pair.1 * gaugeWeight incidence K pair.1 *
        (wilsonSpin B pair.2 * gaugeWeight incidence K pair.2))]
  rw [Fintype.sum_prod_type_right]
  exact Finset.sum_nonneg (fun q _ => gauge_inner_q_nonneg incidence K hK A B q)


theorem gaugeWilsonExpectation_mul_le_symmDiff
    (incidence : P -> Finset E) (K : P -> Real)
    (hK : forall p, 0 <= K p) (A B : Finset E) :
    gaugeWilsonExpectation incidence K A * gaugeWilsonExpectation incidence K B <=
      gaugeWilsonExpectation incidence K (A ∆ B) := by
  unfold gaugeWilsonExpectation
  have hZ : 0 < gaugePartition incidence K := gaugePartition_pos incidence K
  rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) hZ]
  calc
    gaugeWilsonNumerator incidence K A * gaugeWilsonNumerator incidence K B *
        gaugePartition incidence K <=
      (gaugeWilsonNumerator incidence K (A ∆ B) *
          gaugePartition incidence K) * gaugePartition incidence K :=
        mul_le_mul_of_nonneg_right
          (gaugeWilsonNumerator_mul_le incidence K hK A B) hZ.le
    _ = gaugeWilsonNumerator incidence K (A ∆ B) *
        (gaugePartition incidence K * gaugePartition incidence K) := by ring


end
end StatMech.FrontierA
