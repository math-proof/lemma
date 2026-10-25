/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AnisotropicSquareTorusKacWard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalMultiaffine
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPolygonGlobalReduction.Part6
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingSymbol.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.Simon.Part3
import Def.StatisticalMechanics.Code.FrontierA.AnisotropicSquareTorusKacWard
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager


theorem squareTorusWeightedSpinScalePolynomial_eval
    (L : Nat) [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → Complex)
    (a b : Fin 2) (t : Complex) :
    (squareTorusWeightedSpinScalePolynomial L weight a b).eval t =
      ons_weightedSpinCharacterSum L (fun edge ↦ t * weight edge) a b := by
  classical
  unfold squareTorusWeightedSpinScalePolynomial
    ons_weightedSpinCharacterSum
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro F hF
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  ring

theorem weightedPhase_scale
    (L : Nat) (weight : Sym2 (ZMod L × ZMod L) → Complex)
    (a b : Fin 2) (t : Complex) :
    ons_KWmatWeightedPhase L (fun edge ↦ t * weight edge) ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b) =
      t • ons_KWmatWeightedPhase L weight ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b) := by
  ext d₂ d₁
  simp only [ons_KWmatWeightedPhase, ons_KWmatWeighted,
    Matrix.smul_apply, smul_eq_mul]
  by_cases hstep : d₂.1 = ons_dirStep L d₁.2 d₁.1
  · rw [if_pos hstep, if_pos hstep]
    ring
  · rw [if_neg hstep, if_neg hstep]
    simp


theorem squareTorus_weightedSpin_sq_eq_det
    (L : Nat) [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → Complex)
    (a b : Fin 2) :
    ons_weightedSpinCharacterSum L weight a b ^ 2 =
      (1 - ons_KWmatWeightedPhase L weight ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b)).det := by
  classical
  let M := ons_KWmatWeightedPhase L weight ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b)
  let P := kwDetScalePolynomial M
  let Q := (squareTorusWeightedSpinScalePolynomial L weight a b) ^ 2
  let card : Real := Fintype.card (ons_Dart L)
  let radius : Real := (2 * card ^ 2)⁻¹
  let B : Real := 1 + ∑ edge : Sym2 (ZMod L × ZMod L), ‖weight edge‖
  let delta : Real := radius / B
  have hcard : 0 < card := by
    dsimp only [card]
    exact_mod_cast Fintype.card_pos
  have hradius : 0 < radius := by
    dsimp only [radius]
    positivity
  have hB : 0 < B := by
    dsimp only [B]
    positivity
  have hdelta : 0 < delta := by
    dsimp only [delta]
    positivity
  have hedgeB (edge : Sym2 (ZMod L × ZMod L)) : ‖weight edge‖ ≤ B := by
    dsimp only [B]
    have hsingle : ‖weight edge‖ ≤
        ∑ e : Sym2 (ZMod L × ZMod L), ‖weight e‖ :=
      Finset.single_le_sum (fun e _ ↦ norm_nonneg (weight e))
        (Finset.mem_univ edge)
    linarith
  have heval (r : Real) (hr : r ∈ Set.Ioo (0 : Real) delta) :
      P.eval (r : Complex) = Q.eval (r : Complex) := by
    let scaled : Sym2 (ZMod L × ZMod L) → Complex :=
      fun edge ↦ (r : Complex) * weight edge
    let q : Real := r * B
    have hq : 0 ≤ q := mul_nonneg hr.1.le hB.le
    have hscaled (edge : Sym2 (ZMod L × ZMod L)) :
        ‖scaled edge‖ ≤ q := by
      dsimp only [scaled, q]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr.1]
      exact mul_le_mul_of_nonneg_left (hedgeB edge) hr.1.le
    have hsmall : q < (2 * (Fintype.card (ons_Dart L) : Real) ^ 2)⁻¹ := by
      have := hr.2
      dsimp only [delta, radius, card] at this
      have hmul := (lt_div_iff₀ hB).mp this
      simpa only [q] using hmul
    have hroot := ons_weightedRootIdentity_unconditional L
      a b scaled q hq hscaled hsmall
    have hsquare := ons_KWmatWeightedPhase_detWalkRoot_sq
      L scaled a b q hq hscaled hsmall
    have hdet :
        (1 - ons_KWmatWeightedPhase L scaled ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b)).det =
        ons_weightedSpinCharacterSum L scaled a b ^ 2 := by
      rw [← hsquare, hroot]
    dsimp only [P, Q]
    rw [kwDetScalePolynomial_eval, Polynomial.eval_pow,
      squareTorusWeightedSpinScalePolynomial_eval]
    rw [← weightedPhase_scale]
    exact hdet
  have hinfinite : Set.Infinite {z : Complex | P.eval z = Q.eval z} := by
    have hinterval : Set.Infinite (Set.Ioo (0 : Real) delta) :=
      Set.Ioo_infinite hdelta
    have himage : Set.Infinite
        ((fun r : Real ↦ (r : Complex)) '' Set.Ioo (0 : Real) delta) :=
      hinterval.image Complex.ofReal_injective.injOn
    apply himage.mono
    rintro z ⟨r, hr, rfl⟩
    exact heval r hr
  have hpoly : P = Q := Polynomial.eq_of_infinite_eval_eq P Q hinfinite
  have hone := congrArg (Polynomial.eval (1 : Complex)) hpoly
  dsimp only [P, Q] at hone
  rw [kwDetScalePolynomial_eval, Polynomial.eval_pow,
    squareTorusWeightedSpinScalePolynomial_eval] at hone
  simpa [M] using hone.symm


end StatMech.FrontierA
