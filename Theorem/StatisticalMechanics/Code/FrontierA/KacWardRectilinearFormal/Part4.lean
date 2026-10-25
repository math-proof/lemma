/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearFormal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearDeletion.Part2
import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalMultiaffine
import Def.StatisticalMechanics.Code.FrontierA.KacWardRectilinearFormal.Part4
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

open StatMech.Onsager


theorem norm_kwGraphFormalBucketTerm_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ) (weight : Sym2 V → ℂ)
    (r : ℕ) (m : Sym2 V →₀ ℕ) :
    ‖kwGraphFormalBucketTerm G phase weight r m‖ ≤
      ∑ loop : Fin (r + 1) → G.Dart,
        if kwGraphLoopExponent G loop = m then
          ‖ons_loopWeight (kwGraphTransition G weight phase) loop‖
        else 0 := by
  unfold kwGraphFormalBucketTerm
  rw [Finset.sum_div, Finset.sum_mul]
  calc
    ‖∑ loop : Fin (r + 1) → G.Dart,
        (if kwGraphLoopExponent G loop = m then
          kwGraphLoopScalar G phase loop else 0) /
            ((r : ℂ) + 1) * ons_mvMonomialValue weight m‖ ≤
        ∑ loop : Fin (r + 1) → G.Dart,
          ‖(if kwGraphLoopExponent G loop = m then
            kwGraphLoopScalar G phase loop else 0) /
              ((r : ℂ) + 1) * ons_mvMonomialValue weight m‖ :=
      norm_sum_le _ _
    _ ≤ ∑ loop : Fin (r + 1) → G.Dart,
        if kwGraphLoopExponent G loop = m then
          ‖ons_loopWeight (kwGraphTransition G weight phase) loop‖
        else 0 := by
      apply Finset.sum_le_sum
      intro loop _
      by_cases heq : kwGraphLoopExponent G loop = m
      · rw [if_pos heq, if_pos heq, ← heq,
          kwGraphLoopWeight_factor]
        rw [norm_mul, norm_div, norm_mul]
        have hden : 1 ≤ ‖(r : ℂ) + 1‖ := by
          rw [show (r : ℂ) + 1 = ((r + 1 : ℕ) : ℂ) by norm_num,
            norm_natCast]
          norm_num
        exact mul_le_mul_of_nonneg_right
          (div_le_self (norm_nonneg (kwGraphLoopScalar G phase loop)) hden)
          (norm_nonneg (ons_mvMonomialValue weight
            (kwGraphLoopExponent G loop)))
      · simp [heq]

theorem tsum_norm_kwGraphFormalBucketTerm_le_loopSum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ) (weight : Sym2 V → ℂ) (r : ℕ) :
    (∑' m : Sym2 V →₀ ℕ,
      ‖kwGraphFormalBucketTerm G phase weight r m‖) ≤
      ∑ loop : Fin (r + 1) → G.Dart,
        ‖ons_loopWeight (kwGraphTransition G weight phase) loop‖ := by
  classical
  let exponent := fun loop : Fin (r + 1) → G.Dart ↦
    kwGraphLoopExponent G loop
  let S : Finset (Sym2 V →₀ ℕ) := Finset.univ.image exponent
  have hterm : Summable fun m : Sym2 V →₀ ℕ ↦
      ‖kwGraphFormalBucketTerm G phase weight r m‖ := by
    apply summable_of_ne_finset_zero (s := S)
    intro m hm
    have hnone : ∀ loop : Fin (r + 1) → G.Dart,
        kwGraphLoopExponent G loop ≠ m := by
      intro loop heq
      apply hm
      simp [S, exponent, ← heq]
    simp [kwGraphFormalBucketTerm, hnone]
  let major := fun m : Sym2 V →₀ ℕ ↦
    ∑ loop : Fin (r + 1) → G.Dart,
      if kwGraphLoopExponent G loop = m then
        ‖ons_loopWeight (kwGraphTransition G weight phase) loop‖
      else 0
  have hmajor : Summable major := by
    apply summable_of_ne_finset_zero (s := S)
    intro m hm
    have hnone : ∀ loop : Fin (r + 1) → G.Dart,
        kwGraphLoopExponent G loop ≠ m := by
      intro loop heq
      apply hm
      simp [S, exponent, ← heq]
    simp [major, hnone]
  calc
    (∑' m : Sym2 V →₀ ℕ,
        ‖kwGraphFormalBucketTerm G phase weight r m‖) ≤
        ∑' m : Sym2 V →₀ ℕ, major m :=
      Summable.tsum_le_tsum
        (fun m ↦ norm_kwGraphFormalBucketTerm_le
          G phase weight r m) hterm hmajor
    _ = _ := ons_tsum_finite_exponent_buckets_real exponent
      (fun loop ↦ ‖ons_loopWeight
        (kwGraphTransition G weight phase) loop‖)

theorem kw_summable_norm_GraphFormalBucketTerm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ) (weight : Sym2 V → ℂ)
    (q : ℝ) (hq : 0 ≤ q)
    (hentry : ∀ dart next,
      ‖kwGraphTransition G weight phase dart next‖ ≤ q)
    (hcard : (Fintype.card G.Dart : ℝ) * q < 1) :
    Summable fun r : ℕ ↦
      ∑' m : Sym2 V →₀ ℕ,
        ‖kwGraphFormalBucketTerm G phase weight r m‖ := by
  let M := kwGraphTransition G weight phase
  have hC0 : 0 ≤ (Fintype.card G.Dart : ℝ) := by positivity
  have hgeomNorm : ‖(Fintype.card G.Dart : ℝ) * q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC0 hq)]
    exact hcard
  have hgeom : Summable fun r : ℕ ↦
      ((Fintype.card G.Dart : ℝ) * q) ^ (r + 1) :=
    (summable_nat_add_iff 1).2 (summable_geometric_of_norm_lt_one hgeomNorm)
  apply Summable.of_nonneg_of_le
    (fun r ↦ tsum_nonneg (fun m ↦ norm_nonneg _)) (fun r ↦ ?_) hgeom
  calc
    (∑' m : Sym2 V →₀ ℕ,
        ‖kwGraphFormalBucketTerm G phase weight r m‖) ≤
      ∑ loop : Fin (r + 1) → G.Dart, ‖ons_loopWeight M loop‖ :=
        tsum_norm_kwGraphFormalBucketTerm_le_loopSum G phase weight r
    _ ≤ ∑ _loop : Fin (r + 1) → G.Dart, q ^ (r + 1) := by
      apply Finset.sum_le_sum
      intro loop _
      exact norm_ons_loopWeight_le_pow M q hq hentry loop
    _ = ((Fintype.card G.Dart : ℝ) * q) ^ (r + 1) := by
      simp
      ring

theorem kw_summable_norm_GraphFormalBucketTerm_fixed
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ) (weight : Sym2 V → ℂ)
    (r : ℕ) :
    Summable fun m : Sym2 V →₀ ℕ ↦
      ‖kwGraphFormalBucketTerm G phase weight r m‖ := by
  classical
  let exponent := fun loop : Fin (r + 1) → G.Dart ↦
    kwGraphLoopExponent G loop
  let S : Finset (Sym2 V →₀ ℕ) := Finset.univ.image exponent
  apply summable_of_ne_finset_zero (s := S)
  intro m hm
  have hnone : ∀ loop : Fin (r + 1) → G.Dart,
      kwGraphLoopExponent G loop ≠ m := by
    intro loop heq
    apply hm
    simp [S, exponent, ← heq]
  simp [kwGraphFormalBucketTerm, hnone]

theorem kw_summable_norm_GraphFormalBucketTerm_product
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ) (weight : Sym2 V → ℂ)
    (q : ℝ) (hq : 0 ≤ q)
    (hentry : ∀ dart next,
      ‖kwGraphTransition G weight phase dart next‖ ≤ q)
    (hcard : (Fintype.card G.Dart : ℝ) * q < 1) :
    Summable fun p : ℕ × (Sym2 V →₀ ℕ) ↦
      ‖kwGraphFormalBucketTerm G phase weight p.1 p.2‖ := by
  rw [summable_prod_of_nonneg (fun _ ↦ norm_nonneg _)]
  constructor
  · intro r
    exact kw_summable_norm_GraphFormalBucketTerm_fixed
      G phase weight r
  · exact kw_summable_norm_GraphFormalBucketTerm
      G phase weight q hq hentry hcard

theorem kw_summable_GraphFormalBucketTerm_product
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ) (weight : Sym2 V → ℂ)
    (q : ℝ) (hq : 0 ≤ q)
    (hentry : ∀ dart next,
      ‖kwGraphTransition G weight phase dart next‖ ≤ q)
    (hcard : (Fintype.card G.Dart : ℝ) * q < 1) :
    Summable fun p : ℕ × (Sym2 V →₀ ℕ) ↦
      kwGraphFormalBucketTerm G phase weight p.1 p.2 :=
  Summable.of_norm <| kw_summable_norm_GraphFormalBucketTerm_product
    G phase weight q hq hentry hcard

theorem kwGraphFormalLog_evalTerm_eq_bucketTsum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ) (weight : Sym2 V → ℂ)
    (m : Sym2 V →₀ ℕ) :
    MvPowerSeries.coeff m (kwGraphFormalLog G phase) *
        ons_mvMonomialValue weight m =
      ∑' r : ℕ, -kwGraphFormalBucketTerm G phase weight r m / 2 := by
  change kwGraphFormalLogCoeff G phase m *
    ons_mvMonomialValue weight m = _
  rw [kwGraphFormalLogCoeff_eq_tsum]
  calc
    (-(∑' r : ℕ,
        (∑ loop : Fin (r + 1) → G.Dart,
          if kwGraphLoopExponent G loop = m then
            kwGraphLoopScalar G phase loop
          else 0) / ((r : ℂ) + 1)) / 2) *
        ons_mvMonomialValue weight m =
      -(∑' r : ℕ,
        ((∑ loop : Fin (r + 1) → G.Dart,
          if kwGraphLoopExponent G loop = m then
            kwGraphLoopScalar G phase loop
          else 0) / ((r : ℂ) + 1)) *
          ons_mvMonomialValue weight m) / 2 := by
            rw [tsum_mul_right]
            ring
    _ = ∑' r : ℕ,
        -kwGraphFormalBucketTerm G phase weight r m / 2 := by
      rw [← tsum_neg, ← tsum_div_const]
      apply tsum_congr
      intro r
      rfl

theorem kw_MvSeriesEvalSummable_GraphFormalLog
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ) (weight : Sym2 V → ℂ)
    (q : ℝ) (hq : 0 ≤ q)
    (hentry : ∀ dart next,
      ‖kwGraphTransition G weight phase dart next‖ ≤ q)
    (hcard : (Fintype.card G.Dart : ℝ) * q < 1) :
    ons_MvSeriesEvalSummable (kwGraphFormalLog G phase) weight := by
  let term := fun r : ℕ ↦ fun m : Sym2 V →₀ ℕ ↦
    kwGraphFormalBucketTerm G phase weight r m
  have hnorm : Summable fun p : ℕ × (Sym2 V →₀ ℕ) ↦
      ‖term p.1 p.2‖ :=
    kw_summable_norm_GraphFormalBucketTerm_product
      G phase weight q hq hentry hcard
  have hnormScaled : Summable fun p : ℕ × (Sym2 V →₀ ℕ) ↦
      ‖-term p.1 p.2 / 2‖ := by
    have hdiv := hnorm.div_const 2
    simpa only [norm_div, norm_neg, Complex.norm_ofNat] using hdiv
  have hswap : Summable fun p : (Sym2 V →₀ ℕ) × ℕ ↦
      ‖-term p.2 p.1 / 2‖ := by
    simpa only [Function.comp_apply] using
      ((Equiv.prodComm (Sym2 V →₀ ℕ) ℕ).summable_iff.mpr hnormScaled)
  have houter : Summable fun m : Sym2 V →₀ ℕ ↦
      ∑' r : ℕ, ‖-term r m / 2‖ := hswap.prod
  apply Summable.of_nonneg_of_le
    (fun m ↦ norm_nonneg _) (fun m ↦ ?_) houter
  rw [kwGraphFormalLog_evalTerm_eq_bucketTsum]
  have hfixedNorm : Summable fun r : ℕ ↦ ‖-term r m / 2‖ := by
    simpa only [Function.comp_apply] using
      hswap.comp_injective (i := fun r : ℕ ↦ (m, r))
        (fun _ _ h ↦ congrArg Prod.snd h)
  exact norm_tsum_le_tsum_norm hfixedNorm

theorem kw_mvSeriesEval_GraphFormalLog
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ) (weight : Sym2 V → ℂ)
    (q : ℝ) (hq : 0 ≤ q)
    (hentry : ∀ dart next,
      ‖kwGraphTransition G weight phase dart next‖ ≤ q)
    (hcard : (Fintype.card G.Dart : ℝ) * q < 1) :
    ons_mvSeriesEval (kwGraphFormalLog G phase) weight =
      -(∑' r : ℕ,
        (∑ loop : Fin (r + 1) → G.Dart,
          ons_loopWeight (kwGraphTransition G weight phase) loop) /
            ((r : ℂ) + 1)) / 2 := by
  let term := fun r : ℕ ↦ fun m : Sym2 V →₀ ℕ ↦
    kwGraphFormalBucketTerm G phase weight r m
  have hterm : Summable (Function.uncurry term) :=
    kw_summable_GraphFormalBucketTerm_product
      G phase weight q hq hentry hcard
  have hscaled : Summable (Function.uncurry fun r m ↦ -term r m / 2) :=
    hterm.neg.div_const 2
  unfold ons_mvSeriesEval
  change (∑' m : Sym2 V →₀ ℕ,
      kwGraphFormalLogCoeff G phase m *
        ons_mvMonomialValue weight m) = _
  simp_rw [kwGraphFormalLogCoeff_eq_tsum]
  calc
    (∑' m : Sym2 V →₀ ℕ,
        (-(∑' r : ℕ,
          (∑ loop : Fin (r + 1) → G.Dart,
            if kwGraphLoopExponent G loop = m then
              kwGraphLoopScalar G phase loop
            else 0) / ((r : ℂ) + 1)) / 2) *
          ons_mvMonomialValue weight m) =
        ∑' m, ∑' r, -term r m / 2 := by
      apply tsum_congr
      intro m
      calc
        (-(∑' r : ℕ,
            (∑ loop : Fin (r + 1) → G.Dart,
              if kwGraphLoopExponent G loop = m then
                kwGraphLoopScalar G phase loop
              else 0) / ((r : ℂ) + 1)) / 2) *
            ons_mvMonomialValue weight m =
          -(∑' r : ℕ,
            ((∑ loop : Fin (r + 1) → G.Dart,
              if kwGraphLoopExponent G loop = m then
                kwGraphLoopScalar G phase loop
              else 0) / ((r : ℂ) + 1)) *
              ons_mvMonomialValue weight m) / 2 := by
                rw [tsum_mul_right]
                ring
        _ = ∑' r, -term r m / 2 := by
          rw [← tsum_neg, ← tsum_div_const]
          apply tsum_congr
          intro r
          rfl
    _ = ∑' r, ∑' m, -term r m / 2 := hscaled.tsum_comm
    _ = ∑' r : ℕ,
        -(∑ loop : Fin (r + 1) → G.Dart,
          ons_loopWeight (kwGraphTransition G weight phase) loop) /
            ((r : ℂ) + 1) / 2 := by
      apply tsum_congr
      intro r
      rw [tsum_div_const, tsum_neg]
      dsimp only [term]
      simp only [kwGraphFormalBucketTerm]
      rw [kwGraphFormalBucket_eval_div_eq_loopSum]
      ring
    _ = ∑' r : ℕ,
        -((∑ loop : Fin (r + 1) → G.Dart,
          ons_loopWeight (kwGraphTransition G weight phase) loop) /
            ((r : ℂ) + 1)) / 2 := by
      apply tsum_congr
      intro r
      ring
    _ = _ := by rw [tsum_div_const, tsum_neg]


theorem kw_mvSeriesEval_GraphFormalRoot
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ) (weight : Sym2 V → ℂ)
    (q : ℝ) (hq : 0 ≤ q)
    (hentry : ∀ dart next,
      ‖kwGraphTransition G weight phase dart next‖ ≤ q)
    (hcard : (Fintype.card G.Dart : ℝ) * q < 1) :
    ons_mvSeriesEval (kwGraphFormalRoot G phase) weight =
      ons_detWalkRoot (kwGraphTransition G weight phase) := by
  rw [kwGraphFormalRoot,
    ons_mvSeriesEval_subst_exp
      (kwGraphFormalLog G phase) weight
      (kwGraphFormalLog_hasSubst G phase)
      (kw_MvSeriesEvalSummable_GraphFormalLog
        G phase weight q hq hentry hcard),
    kw_mvSeriesEval_GraphFormalLog G phase weight q hq hentry hcard]
  rfl

theorem kw_MvSeriesEvalSummable_GraphFormalRoot
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ) (weight : Sym2 V → ℂ)
    (q : ℝ) (hq : 0 ≤ q)
    (hentry : ∀ dart next,
      ‖kwGraphTransition G weight phase dart next‖ ≤ q)
    (hcard : (Fintype.card G.Dart : ℝ) * q < 1) :
    ons_MvSeriesEvalSummable (kwGraphFormalRoot G phase) weight := by
  unfold kwGraphFormalRoot
  exact ons_MvSeriesEvalSummable_subst_exp
    (kwGraphFormalLog G phase) weight
    (kwGraphFormalLog_hasSubst G phase)
    (kw_MvSeriesEvalSummable_GraphFormalLog
      G phase weight q hq hentry hcard)

theorem kw_mvMonomialValue_scaleGraphEdgeWeight
    {V : Type*} [DecidableEq V]
    (weight : Sym2 V → ℂ) (edge : Sym2 V) (t : ℂ)
    (m : Sym2 V →₀ ℕ) :
    ons_mvMonomialValue (kwScaleGraphEdgeWeight weight edge t) m =
      t ^ m edge * ons_mvMonomialValue weight m := by
  classical
  unfold ons_mvMonomialValue
  calc
    m.prod (fun f n ↦ kwScaleGraphEdgeWeight weight edge t f ^ n) =
        m.prod (fun f n ↦
          (if f = edge then t ^ n else 1) * weight f ^ n) := by
      apply Finsupp.prod_congr
      intro f _
      unfold kwScaleGraphEdgeWeight
      by_cases hfe : f = edge
      · simp [hfe, mul_pow]
      · simp [hfe]
    _ = m.prod (fun f n ↦ if f = edge then t ^ n else 1) *
          m.prod (fun f n ↦ weight f ^ n) := Finsupp.prod_mul
    _ = t ^ m edge * m.prod (fun f n ↦ weight f ^ n) := by
      congr 1
      unfold Finsupp.prod
      by_cases hedge : edge ∈ m.support
      · rw [Finset.prod_eq_single edge]
        · simp
        · intro f _ hfe
          simp [hfe]
        · exact fun hnot ↦ (hnot hedge).elim
      · have hzero : m edge = 0 := Finsupp.notMem_support_iff.mp hedge
        rw [hzero, pow_zero]
        apply Finset.prod_eq_one
        intro f hf
        have hfe : f ≠ edge := by
          intro h
          subst f
          exact hedge hf
        simp [hfe]

end StatMech.FrontierA
