/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.LeeYangPolynomial
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangSingleEdge.Part3
import Theorem.StatisticalMechanics.Code.FrontierC.LeeYangSymmetry.Part2
import Def.StatisticalMechanics.Code.FrontierA.LeeYangAsano
open scoped ComplexConjugate


namespace StatMech.FrontierA

theorem asanoContract_stable {I : Type*} [DecidableEq I]
    (p : (I → ℂ) → ℂ) (hpAff : IsMultiAffine p)
    (hpStable : PolydiscStable p) {i j : I} (hij : i ≠ j) :
    PolydiscStable (asanoContract p i j) := by
  intro z hz
  let z00 := Function.update (Function.update z i 0) j 0
  let z10 := Function.update (Function.update z i 1) j 0
  let z01 := Function.update (Function.update z i 0) j 1
  let z11 := Function.update (Function.update z i 1) j 1
  let A := p z00
  let E := p z10 + p z01 - 2 * p z00
  let D := p z11 - p z10 - p z01 + p z00
  have hdiag (t : ℂ) :
      p (Function.update (Function.update z i t) j t) =
        A + E * t + D * t ^ 2 := by
    rw [Function.update_comm hij t t z]
    rw [hpAff i (Function.update z j t) t]
    rw [← Function.update_comm hij 0 t z,
      ← Function.update_comm hij 1 t z]
    rw [hpAff j (Function.update z i 0) t,
      hpAff j (Function.update z i 1) t]
    simp only [A, E, D, z00, z10, z01, z11]
    ring
  have hquad : ∀ t : ℂ, ‖t‖ < 1 → A + E * t + D * t ^ 2 ≠ 0 := by
    intro t ht hzero
    apply hpStable (Function.update (Function.update z i t) j t)
    · intro k
      by_cases hki : k = i
      · subst k
        simp [hij, ht]
      · by_cases hkj : k = j
        · subst k
          simp [ht]
        · simp [hki, hkj, hz]
    · rw [hdiag]
      exact hzero
  have hc := asano_quadratic_contraction A E D (z i) hquad (hz i)
  simpa only [asanoContract, A, D, z00, z10, z01, z11, mul_comm] using hc

theorem asanoContract_multiAffine {I : Type*} [DecidableEq I]
    (p : (I → ℂ) → ℂ) (hp : IsMultiAffine p) {i j : I} (hij : i ≠ j) :
    IsMultiAffine (asanoContract p i j) := by
  intro k z t
  by_cases hki : k = i
  · subst k
    simp [asanoContract]
  · by_cases hkj : k = j
    · subst k
      have hcanon (u a b : ℂ) :
          Function.update (Function.update (Function.update z j u) i a) j b =
            Function.update (Function.update z i a) j b := by
        funext x
        by_cases hxj : x = j
        · subst x
          simp
        · by_cases hxi : x = i
          · subst x
            simp [hij]
          · simp [hxj, hxi]
      simp only [asanoContract]
      simp_rw [hcanon]
      simp [hij]
    · have hcomm (a b u : ℂ) :
          Function.update (Function.update (Function.update z k u) i a) j b =
            Function.update (Function.update (Function.update z i a) j b) k u := by
          funext x
          by_cases hxk : x = k
          · subst x
            simp [hki, hkj]
          · by_cases hxi : x = i
            · subst x
              simp [hij, Ne.symm hki]
            · by_cases hxj : x = j
              · subst x
                simp [Ne.symm hkj]
              · simp [hxk, hxi, hxj]
      have hslice (a b u : ℂ) :
          p (Function.update (Function.update (Function.update z k u) i a) j b) =
            p (Function.update
                (Function.update (Function.update z i a) j b) k 0) +
              u * (p (Function.update
                    (Function.update (Function.update z i a) j b) k 1) -
                p (Function.update
                    (Function.update (Function.update z i a) j b) k 0)) := by
        rw [hcomm]
        exact hp k (Function.update (Function.update z i a) j b) u
      simp only [asanoContract]
      rw [hslice 0 0 t, hslice 1 1 t, hslice 1 0 t, hslice 0 1 t]
      rw [hcomm 0 0 0, hcomm 1 1 0, hcomm 1 0 0, hcomm 0 1 0,
        hcomm 0 0 1, hcomm 1 1 1, hcomm 1 0 1, hcomm 0 1 1]
      simp [Ne.symm hki]
      ring

theorem leeYang_edgeFactor_ne_zero {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    1 + a * b + (r : ℂ) * (a + b) ≠ 0 := by
  intro hzero
  have haSq : Complex.normSq a < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg a]
  have hid : Complex.normSq (1 + (r : ℂ) * a) -
      Complex.normSq (a + (r : ℂ)) =
        (1 - r ^ 2) * (1 - Complex.normSq a) := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.one_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hsq : Complex.normSq (a + (r : ℂ)) ≤
      Complex.normSq (1 + (r : ℂ) * a) := by
    rw [sub_eq_iff_eq_add] at hid
    rw [hid]
    have hrSqLe : r ^ 2 ≤ 1 := by nlinarith [sq_nonneg r]
    nlinarith
  have hnorm : ‖a + (r : ℂ)‖ ≤ ‖1 + (r : ℂ) * a‖ := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hsq
    nlinarith [norm_nonneg (a + (r : ℂ)), norm_nonneg (1 + (r : ℂ) * a)]
  have hrelation : 1 + (r : ℂ) * a = -(b * (a + (r : ℂ))) := by
    linear_combination hzero
  have hdenom : 0 < ‖a + (r : ℂ)‖ := by
    rw [norm_pos_iff]
    intro hden
    have haeq : a = -(r : ℂ) := by linear_combination hden
    rw [haeq] at hzero
    have hrSq : r ^ 2 = 1 := by
      have hc : (1 : ℂ) - (r : ℂ) ^ 2 = 0 := by
        linear_combination hzero
      have hrreal : 1 - r ^ 2 = 0 := by
        apply Complex.ofReal_eq_zero.mp
        simpa using hc
      nlinarith
    have hrEq : r = 1 := by nlinarith
    subst r
    simp at haeq
    rw [haeq] at ha
    norm_num at ha
  rw [hrelation, norm_neg, norm_mul] at hnorm
  nlinarith [mul_lt_mul_of_pos_right hb hdenom]

end StatMech.FrontierA
