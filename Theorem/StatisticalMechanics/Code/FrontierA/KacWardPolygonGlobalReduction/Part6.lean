/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonGlobalReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardFinitePolygonEar.Part12
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardUnitCycleReduction
import Def.StatisticalMechanics.Code.FrontierA.KacWardPolygonGlobalReduction.Part5
open scoped BigOperators
open Finset SimpleGraph Polynomial


namespace StatMech.FrontierA

open StatMech.Onsager

open StatMech.Ising

universe u


theorem kwEvenScalePolynomial_eval
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : Sym2 V → ℂ) (t : ℂ) :
    (kwEvenScalePolynomial G weight).eval t =
      kwEvenPolynomial G (fun edge ↦ t * weight edge) := by
  classical
  unfold kwEvenScalePolynomial kwEvenPolynomial evenSubgraphs
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro F hF
  rw [Finset.prod_mul_distrib]
  simp
  ring


theorem kacWard_straightLine_trivalent_of_oddCycleTurning
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (hdeg : ∀ vertex, G.degree vertex ≤ 3)
    (hturning : KWStraightLineCycleOddTurning G embedding)
    (weight : Sym2 V → ℂ) :
    (1 - kwGraphTransition G weight embedding.turnPhase).det =
      (kwEvenPolynomial G weight) ^ 2 := by
  let M := kwGraphTransition G weight embedding.turnPhase
  let P := kwDetScalePolynomial M
  let Q := (kwEvenScalePolynomial G weight) ^ 2
  let card : ℝ := Fintype.card G.Dart
  let q : ℝ := (2 * (1 + card))⁻¹
  let B : ℝ := ∑ dart : G.Dart, ∑ next : G.Dart, ‖M dart next‖
  let delta : ℝ := q / (1 + B)
  have hcard0 : 0 ≤ card := by positivity
  have hq : 0 < q := by
    dsimp only [q]
    positivity
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity
  have hdelta : 0 < delta := by
    dsimp only [delta]
    positivity
  have hcardq : card * q < 1 := by
    dsimp only [q]
    rw [mul_inv_lt_iff₀ (by positivity : 0 < 2 * (1 + card))]
    nlinarith
  have hraw (dart next : G.Dart) : ‖M dart next‖ ≤ B := by
    dsimp only [B]
    exact (Finset.single_le_sum
      (fun d _ ↦ Finset.sum_nonneg fun e _ ↦ norm_nonneg (M d e))
      (Finset.mem_univ dart)).trans' <|
        Finset.single_le_sum
          (fun e _ ↦ norm_nonneg (M dart e)) (Finset.mem_univ next)
  have heval (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) delta) :
      P.eval (r : ℂ) = Q.eval (r : ℂ) := by
    have hrnorm : ‖(r : ℂ)‖ = r := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr.1]
    have hentry : ∀ dart next,
        ‖kwGraphTransition G (fun edge ↦ (r : ℂ) * weight edge)
          embedding.turnPhase dart next‖ ≤ q := by
      intro dart next
      rw [kwGraphTransition_smulWeight, norm_mul, hrnorm]
      have hlt : r * B < q := by
        have hden : 0 < 1 + B := by positivity
        have := hr.2
        dsimp only [delta] at this
        rw [lt_div_iff₀ hden] at this
        nlinarith
      exact (mul_le_mul_of_nonneg_left
        (hraw dart next) hr.1.le).trans hlt.le
    have hsmall := kacWard_straightLine_trivalent_of_cycleCoeff
      G embedding hdeg
        (kwGraphFormalLogCoeff_cycle_eq_one_of_oddCycleTurning
          G embedding hdeg hturning)
      (fun edge ↦ (r : ℂ) * weight edge) q hq.le hentry hcardq
    dsimp only [P, Q]
    rw [kwDetScalePolynomial_eval,
      Polynomial.eval_pow, kwEvenScalePolynomial_eval]
    have hmatrix : (r : ℂ) • M =
        kwGraphTransition G (fun edge ↦ (r : ℂ) * weight edge)
          embedding.turnPhase := by
      ext dart next
      change (r : ℂ) * M dart next = _
      dsimp only [M]
      rw [kwGraphTransition_smulWeight]
    rw [hmatrix]
    exact hsmall
  have hinfinite : Set.Infinite
      {z : ℂ | P.eval z = Q.eval z} := by
    have hI : Set.Infinite (Set.Ioo (0 : ℝ) delta) :=
      Set.Ioo_infinite hdelta
    have himage : Set.Infinite
        ((fun r : ℝ ↦ (r : ℂ)) '' Set.Ioo (0 : ℝ) delta) :=
      hI.image Complex.ofReal_injective.injOn
    apply himage.mono
    rintro z ⟨r, hr, rfl⟩
    exact heval r hr
  have hpoly : P = Q :=
    Polynomial.eq_of_infinite_eval_eq P Q hinfinite
  have hone := congrArg (Polynomial.eval (1 : ℂ)) hpoly
  dsimp only [P, Q] at hone
  simpa [kwDetScalePolynomial_eval,
    kwEvenScalePolynomial_eval, M] using hone


theorem kacWard_straightLine_trivalent_allWeights_of_cycleTurning
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (hdeg : ∀ vertex, G.degree vertex ≤ 3)
    (hturning : KWStraightLineCycleTurning G embedding)
    (weight : Sym2 V → ℂ) :
    (1 - kwGraphTransition G weight embedding.turnPhase).det =
      (kwEvenPolynomial G weight) ^ 2 :=
  kacWard_straightLine_trivalent_of_oddCycleTurning G embedding hdeg
    (hturning.toOddTurning G embedding) weight

end StatMech.FrontierA
