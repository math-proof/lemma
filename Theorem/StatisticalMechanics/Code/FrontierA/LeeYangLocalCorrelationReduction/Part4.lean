/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangLocalCorrelationReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangPressurePrimitive.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.FreeBoxSpinLimit
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Def.StatisticalMechanics.Code.FrontierA.LeeYangLocalCorrelationReduction.Part4
open Complex Filter MeasureTheory Metric Set Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.FK StatMech.Ising StatMech.Lattice StatMech.FrontierB
  StatMech.FrontierC StatMech.Sharpness StatMech.Sharpness.FieldGhostDict


theorem leeYangMonomial_anchorSupport_flip
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ConfigSpace V) (z : LeeYangVar G → ℂ) :
    leeYangMonomial (leeYangAnchorSupport G (leeYangFlip s)) z =
      ∏ v : V, if s v = false then z (leeYangAnchor G v) else 1 := by
  unfold leeYangMonomial leeYangAnchorSupport leeYangFlip leeYangAnchor
  rw [Finset.prod_filter]
  simp [Fintype.prod_sum_type]

theorem leeYangSignedProduct_eq_spinProd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ConfigSpace V) (A : Finset V) (q : ℂ) :
    (∏ v : V, if s v = false then
        leeYangSignedDiagonal G A q (leeYangAnchor G v) else 1) =
      (spinProd A s : ℂ) * q ^ minusSpinCount s := by
  rw [show (spinProd A s : ℂ) =
      ∏ v : V, if v ∈ A then (spin s v : ℂ) else 1 by
    calc
      (spinProd A s : ℂ) = ∏ v ∈ A, (spin s v : ℂ) := by
        unfold spinProd
        push_cast
        rfl
      _ = ∏ v : V, if v ∈ A then (spin s v : ℂ) else 1 := by simp]
  rw [show q ^ minusSpinCount s =
      ∏ v : V, if s v = false then q else 1 by
    simp [minusSpinCount, Finset.prod_ite, Finset.prod_const]]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro v hv
  simp only [leeYangSignedDiagonal, leeYangAnchor]
  by_cases hA : v ∈ A <;> cases hs : s v <;> simp [hA, hs, spin]

theorem leeYangSignedDiagonal_empty
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℂ) :
    leeYangSignedDiagonal G ∅ q = leeYangDiagonal G q := by
  funext k
  rcases k with v | he <;> simp [leeYangSignedDiagonal, leeYangDiagonal]

theorem leeYangSignedDiagonal_insert
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (v : V) (hv : v ∉ A) (q : ℂ) :
    leeYangSignedDiagonal G (insert v A) q =
      Function.update (leeYangSignedDiagonal G A q)
        (leeYangAnchor G v) (-q) := by
  funext k
  rcases k with w | he
  · by_cases hwv : w = v
    · subst w
      simp [leeYangSignedDiagonal, leeYangAnchor, hv]
    · simp [leeYangSignedDiagonal, leeYangAnchor, hwv]
  · simp [leeYangSignedDiagonal, leeYangAnchor]

theorem leeYangSignedDiagonal_norm_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) {q : ℂ} (hq : ‖q‖ < 1) :
    ∀ k, ‖leeYangSignedDiagonal G A q k‖ < 1 := by
  intro k
  rcases k with v | he
  · by_cases hv : v ∈ A <;> simp [leeYangSignedDiagonal, hv, hq]
  · simp [leeYangSignedDiagonal]


theorem leeYangContracted_signed_norm_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {beta : ℝ} (hbeta : 0 ≤ beta) {q : ℂ} (hq : ‖q‖ < 1)
    (A : Finset V) :
    ‖leeYangContractedProduct G beta (leeYangSignedDiagonal G A q)‖ ≤
      ((1 + ‖q‖) / (1 - ‖q‖)) ^ A.card *
        ‖leeYangContractedProduct G beta (leeYangDiagonal G q)‖ := by
  induction A using Finset.induction with
  | empty =>
      rw [leeYangSignedDiagonal_empty]
      simp
  | @insert v A hv ih =>
      rw [leeYangSignedDiagonal_insert G A v hv q]
      let z := leeYangSignedDiagonal G A q
      have hz : ∀ k, ‖z k‖ < 1 := leeYangSignedDiagonal_norm_lt G A hq
      have hzi : z (leeYangAnchor G v) = q := by
        simp [z, leeYangSignedDiagonal, leeYangAnchor, hv]
      have hone := multiAffine_sign_update_norm_le
        (leeYangContractedProduct G beta)
        (leeYangContractedProduct_multiAffine G beta)
        (leeYangContractedProduct_stable G hbeta) z hz (leeYangAnchor G v)
      rw [hzi] at hone
      calc
        ‖leeYangContractedProduct G beta
            (Function.update z (leeYangAnchor G v) (-q))‖ ≤
            ((1 + ‖q‖) / (1 - ‖q‖)) *
              ‖leeYangContractedProduct G beta z‖ := hone
        _ ≤ ((1 + ‖q‖) / (1 - ‖q‖)) *
              (((1 + ‖q‖) / (1 - ‖q‖)) ^ A.card *
                ‖leeYangContractedProduct G beta (leeYangDiagonal G q)‖) := by
              apply mul_le_mul_of_nonneg_left ih
              positivity
        _ = ((1 + ‖q‖) / (1 - ‖q‖)) ^ (insert v A).card *
              ‖leeYangContractedProduct G beta (leeYangDiagonal G q)‖ := by
              rw [Finset.card_insert_of_notMem hv, pow_succ]
              ring

theorem leeYangContracted_signed_eq_spin_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : ℝ) (A : Finset V) (q : ℂ) :
    (Real.exp (beta * G.edgeFinset.card) : ℂ) *
        leeYangContractedProduct G beta (leeYangSignedDiagonal G A q) =
      ∑ s : ConfigSpace V, (spinProd A s : ℂ) *
        (zeroFieldInteractionWeight G beta s : ℂ) * q ^ minusSpinCount s := by
  rw [leeYangContractedProduct_eq_sum_sigma, Finset.mul_sum]
  let F : ConfigSpace V → ℂ := fun sigma ↦
    (Real.exp (beta * G.edgeFinset.card) : ℂ) *
      (leeYangChoiceWeight G beta (sigma, leeYangTauOf G sigma) *
        leeYangMonomial (leeYangAnchorSupport G sigma)
          (leeYangSignedDiagonal G A q))
  change (∑ sigma : ConfigSpace V, F sigma) = _
  rw [show (∑ sigma : ConfigSpace V, F sigma) =
      ∑ s : ConfigSpace V, F (leeYangFlipEquiv s) by
        simpa using (Equiv.sum_comp leeYangFlipEquiv F).symm]
  apply Finset.sum_congr rfl
  intro s hs
  have hweight :
      (Real.exp (beta * G.edgeFinset.card) : ℂ) *
          leeYangChoiceWeight G beta
            (leeYangFlip s, leeYangTauOf G (leeYangFlip s)) =
        (zeroFieldInteractionWeight G beta s : ℂ) := by
    rw [leeYangChoiceWeight_eq_ofReal]
    rw [← Complex.ofReal_mul]
    rw [exp_card_mul_leeYangRealChoiceWeight]
    rw [zeroFieldInteractionWeight_flip]
  simp only [F, leeYangFlipEquiv_apply]
  rw [← mul_assoc, hweight, leeYangMonomial_anchorSupport_flip,
    leeYangSignedProduct_eq_spinProd]
  ring

theorem leeYangObservable_fugacity_eq_signed
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : ℝ) (A : Finset V) (h : ℂ) :
    Complex.exp (-(beta : ℂ) * h * Fintype.card V) *
        leeYangComplexFieldObservableNumerator G beta
          (fun s ↦ (spinProd A s : ℂ)) h =
      (Real.exp (beta * G.edgeFinset.card) : ℂ) *
        leeYangContractedProduct G beta
          (leeYangSignedDiagonal G A
            (Complex.exp (-2 * (beta : ℂ) * h))) := by
  rw [leeYangContracted_signed_eq_spin_sum]
  unfold leeYangComplexFieldObservableNumerator
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [← Complex.exp_nat_mul]
  unfold zeroFieldInteractionWeight
  rw [Complex.ofReal_exp]
  rw [show Complex.exp (-(beta : ℂ) * h * Fintype.card V) *
        ((spinProd A s : ℂ) * Complex.exp
          ((beta : ℂ) * (∑ e ∈ G.edgeFinset, bond s e) +
            (beta : ℂ) * h * (∑ v : V, spin s v))) =
      (spinProd A s : ℂ) *
        (Complex.exp (-(beta : ℂ) * h * Fintype.card V) *
          Complex.exp
            ((beta : ℂ) * (∑ e ∈ G.edgeFinset, bond s e) +
              (beta : ℂ) * h * (∑ v : V, spin s v))) by ring]
  rw [← Complex.exp_add]
  conv_rhs =>
    rw [mul_assoc, ← Complex.exp_add]
  rw [sum_spin_eq_card_sub_two_mul_minusSpinCount s]
  push_cast
  ring_nf

theorem leeYangComplexFieldExpectation_spinProd_eq_contractedRatio
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {beta : ℝ} (hbeta : 0 ≤ beta) (A : Finset V) {h : ℂ}
    (hh : h.re ≠ 0) :
    leeYangComplexFieldExpectation G beta (fun s ↦ (spinProd A s : ℂ)) h =
      leeYangContractedProduct G beta
          (leeYangSignedDiagonal G A
            (Complex.exp (-2 * (beta : ℂ) * h))) /
        leeYangContractedProduct G beta
          (leeYangDiagonal G (Complex.exp (-2 * (beta : ℂ) * h))) := by
  let q := Complex.exp (-2 * (beta : ℂ) * h)
  let c : ℂ := Real.exp (beta * G.edgeFinset.card)
  let e := Complex.exp (-(beta : ℂ) * h * Fintype.card V)
  let N := leeYangComplexFieldObservableNumerator G beta
    (fun s ↦ (spinProd A s : ℂ)) h
  let Z := leeYangComplexFieldPartition G beta h
  let P := leeYangContractedProduct G beta (leeYangSignedDiagonal G A q)
  let Q := leeYangContractedProduct G beta (leeYangDiagonal G q)
  have hnum : e * N = c * P := by
    simpa only [e, N, c, P, q] using
      leeYangObservable_fugacity_eq_signed G beta A h
  have hden : e * Z = c * Q := by
    calc
      e * Z = (leeYangComplexPolynomial G beta).eval q := by
        symm
        simpa only [e, Z, q] using
          leeYangComplexFieldPartition_eq_fugacity G beta h
      _ = c * Q := by
        symm
        simpa only [c, Q, q] using leeYangContractedProduct_diagonal G beta q
  have he : e ≠ 0 := Complex.exp_ne_zero _
  have hZ : Z ≠ 0 :=
    leeYangComplexFieldPartition_ne_zero_of_nonneg_re_ne_zero G hbeta hh
  have hQ : Q ≠ 0 := by
    intro hQ0
    rw [hQ0, mul_zero] at hden
    exact mul_ne_zero he hZ hden
  change N / Z = P / Q
  apply (div_eq_div_iff hZ hQ).2
  apply mul_left_cancel₀ he
  calc
    e * (N * Q) = (e * N) * Q := by ring
    _ = (c * P) * Q := by rw [hnum]
    _ = P * (c * Q) := by ring
    _ = P * (e * Z) := by rw [hden]
    _ = e * (P * Z) := by ring

theorem leeYangComplexFieldExpectation_spinProd_norm_le_right
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {beta : ℝ} (hbeta : 0 < beta) (A : Finset V) {h : ℂ}
    (hh : 0 < h.re) :
    ‖leeYangComplexFieldExpectation G beta
        (fun s ↦ (spinProd A s : ℂ)) h‖ ≤
      ((1 + ‖Complex.exp (-2 * (beta : ℂ) * h)‖) /
        (1 - ‖Complex.exp (-2 * (beta : ℂ) * h)‖)) ^ A.card := by
  let q := Complex.exp (-2 * (beta : ℂ) * h)
  have hq : ‖q‖ < 1 := by
    rw [Complex.norm_exp, Real.exp_lt_one_iff]
    norm_num [q, Complex.mul_re]
    nlinarith
  have hratio := leeYangComplexFieldExpectation_spinProd_eq_contractedRatio
    G hbeta.le A (ne_of_gt hh)
  let P := leeYangContractedProduct G beta (leeYangSignedDiagonal G A q)
  let Q := leeYangContractedProduct G beta (leeYangDiagonal G q)
  have hbound : ‖P‖ ≤ ((1 + ‖q‖) / (1 - ‖q‖)) ^ A.card * ‖Q‖ :=
    leeYangContracted_signed_norm_le G hbeta.le hq A
  have hQ : Q ≠ 0 := by
    apply leeYangContractedProduct_stable G hbeta.le
    intro k
    rcases k with v | he
    · exact hq
    · simp [leeYangDiagonal]
  rw [hratio]
  change ‖P / Q‖ ≤ _
  rw [norm_div]
  apply (div_le_iff₀ (norm_pos_iff.mpr hQ)).2
  simpa only [q] using hbound

theorem boxSpinSupport_card_le (d n : ℕ) (A : Finset (Site d)) :
    (boxSpinSupport d n A).card ≤ A.card := by
  have hsub : (boxSpinSupport d n A).image Subtype.val ⊆ A := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa [boxSpinSupport] using hy
  calc
    (boxSpinSupport d n A).card =
        ((boxSpinSupport d n A).image Subtype.val).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ ≤ A.card := Finset.card_le_card hsub


theorem leeYangSpinProductRightBound
    (d : ℕ) {beta : ℝ} (hbeta : 0 < beta) (A : Finset (Site d)) :
    LeeYangSpinProductRightBound d beta A := by
  intro n h hh
  let q := Complex.exp (-2 * (beta : ℂ) * h)
  let c : ℝ := (1 + ‖q‖) / (1 - ‖q‖)
  have hq : ‖q‖ < 1 := by
    rw [Complex.norm_exp, Real.exp_lt_one_iff]
    norm_num [q, Complex.mul_re]
    nlinarith
  have hc : 1 ≤ c := by
    apply (le_div_iff₀ (sub_pos.mpr hq)).2
    dsimp only [c]
    nlinarith [norm_nonneg q]
  have hfinite := leeYangComplexFieldExpectation_spinProd_norm_le_right
    (boxGraph d n) hbeta (boxSpinSupport d n A) hh
  have hcard := boxSpinSupport_card_le d n A
  calc
    ‖leeYangBoxSpinProduct d beta A n h‖ ≤ c ^ (boxSpinSupport d n A).card := by
      simpa only [leeYangBoxSpinProduct, q, c] using hfinite
    _ ≤ c ^ A.card := pow_le_pow_right₀ hc hcard
    _ = leeYangSpinProductRightEnvelope beta A h := by rfl

theorem leeYangComplexFieldPartition_neg
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : ℝ) (h : ℂ) :
    leeYangComplexFieldPartition G beta (-h) =
      leeYangComplexFieldPartition G beta h := by
  unfold leeYangComplexFieldPartition
  rw [← Equiv.sum_comp (flipV_involutive (V := V)).toPerm]
  simp only [Function.Involutive.coe_toPerm]
  apply Finset.sum_congr rfl
  intro s hs
  congr 1
  have hb : (∑ e ∈ G.edgeFinset, bond (flipV s) e) =
      ∑ e ∈ G.edgeFinset, bond s e :=
    Finset.sum_congr rfl (fun e _ ↦ bond_flipV s e)
  have hspin : (∑ x : V, spin (flipV s) x) = -∑ x : V, spin s x := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun x _ ↦ spin_flipV s x)
  rw [hb, hspin]
  push_cast
  ring

theorem leeYangComplexFieldObservable_spinProd_neg
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : ℝ) (h : ℂ) (A : Finset V) :
    leeYangComplexFieldObservableNumerator G beta
        (fun s ↦ (spinProd A s : ℂ)) (-h) =
      (((-1 : ℝ) : ℂ) ^ A.card) *
        leeYangComplexFieldObservableNumerator G beta
          (fun s ↦ (spinProd A s : ℂ)) h := by
  unfold leeYangComplexFieldObservableNumerator
  rw [← Equiv.sum_comp (flipV_involutive (V := V)).toPerm]
  simp only [Function.Involutive.coe_toPerm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hb : (∑ e ∈ G.edgeFinset, bond (flipV s) e) =
      ∑ e ∈ G.edgeFinset, bond s e :=
    Finset.sum_congr rfl (fun e _ ↦ bond_flipV s e)
  have hspin : (∑ x : V, spin (flipV s) x) = -∑ x : V, spin s x := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun x _ ↦ spin_flipV s x)
  rw [hb, hspin, spinProd_flipV]
  push_cast
  ring

theorem leeYangComplexFieldExpectation_spinProd_neg
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : ℝ) (h : ℂ) (A : Finset V) :
    leeYangComplexFieldExpectation G beta
        (fun s ↦ (spinProd A s : ℂ)) (-h) =
      (((-1 : ℝ) : ℂ) ^ A.card) *
        leeYangComplexFieldExpectation G beta
          (fun s ↦ (spinProd A s : ℂ)) h := by
  unfold leeYangComplexFieldExpectation
  rw [leeYangComplexFieldObservable_spinProd_neg,
    leeYangComplexFieldPartition_neg]
  ring


theorem leeYangSpinProductLeftBound
    (d : ℕ) {beta : ℝ} (hbeta : 0 < beta) (A : Finset (Site d)) :
    LeeYangSpinProductLeftBound d beta A := by
  intro n h hh
  have hright := leeYangSpinProductRightBound d hbeta A n (-h)
    (by simpa using neg_pos.mpr hh)
  have hflip := leeYangComplexFieldExpectation_spinProd_neg
    (boxGraph d n) beta h (boxSpinSupport d n A)
  have hnormpow :
      ‖(((-1 : ℝ) : ℂ) ^ (boxSpinSupport d n A).card)‖ = 1 := by
    rw [norm_pow]
    norm_num
  rw [leeYangBoxSpinProduct, hflip, norm_mul, hnormpow, one_mul] at hright
  simpa only [leeYangBoxSpinProduct, leeYangSpinProductRightEnvelope,
    leeYangSpinProductLeftEnvelope, neg_mul, mul_neg, neg_neg] using hright


theorem leeYangBoxSpinProduct_rightHalfPlane
    (d : ℕ) (hd : 1 ≤ d) {beta : ℝ} (hbeta : 0 < beta)
    (A : Finset (Site d)) :
    ∃ g : ℂ → ℂ,
      TendstoLocallyUniformlyOn (leeYangBoxSpinProduct d beta A) g
        atTop {z : ℂ | 0 < z.re} ∧
      DifferentiableOn ℂ g {z : ℂ | 0 < z.re} ∧
      TendstoLocallyUniformlyOn
        (deriv ∘ leeYangBoxSpinProduct d beta A) (deriv g)
        atTop {z : ℂ | 0 < z.re} :=
  leeYangBoxSpinProduct_rightHalfPlane_of_pointwiseBound
    d hd hbeta A (leeYangSpinProductRightBound d hbeta A)


theorem leeYangBoxSpinProduct_leftHalfPlane
    (d : ℕ) (hd : 1 ≤ d) {beta : ℝ} (hbeta : 0 < beta)
    (A : Finset (Site d)) :
    ∃ g : ℂ → ℂ,
      TendstoLocallyUniformlyOn (leeYangBoxSpinProduct d beta A) g
        atTop {z : ℂ | z.re < 0} ∧
      DifferentiableOn ℂ g {z : ℂ | z.re < 0} ∧
      TendstoLocallyUniformlyOn
        (deriv ∘ leeYangBoxSpinProduct d beta A) (deriv g)
        atTop {z : ℂ | z.re < 0} :=
  leeYangBoxSpinProduct_leftHalfPlane_of_pointwiseBound
    d hd hbeta A (leeYangSpinProductLeftBound d hbeta A)

end StatMech.FrontierA
