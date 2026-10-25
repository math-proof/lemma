/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinPolynomial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.KWDetLimit.Part2
import Theorem.StatisticalMechanics.Code.Onsager.SpinAssembly
import Theorem.StatisticalMechanics.Code.Onsager.TorusSpinSectors.Part3
import Def.StatisticalMechanics.Code.Onsager.SpinPolynomial.Part4


namespace StatMech.Onsager

open StatMech.Ising Polynomial

theorem ons_spinKacWardAt_all_of_small (L : ℕ) [Fact (2 < L)]
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hsmall : ∀ x ∈ Set.Ioo (0 : ℝ) epsilon, ons_spinKacWardAt L x) :
    ∀ x : ℝ, ons_spinKacWardAt L x := by
  have hinter : (Set.Ioo (0 : ℝ) epsilon).Infinite :=
    Set.Ioo_infinite hepsilon
  have h11poly : ons_spinPoly11 L ^ 2 = ons_spinDetPoly L 0 0 := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply hinter.mono
    intro x hx
    simp only [Set.mem_setOf_eq, eval_pow, eval_ons_spinPoly11,
      eval_ons_spinDetPoly]
    exact (hsmall x hx).1
  have h01poly : ons_spinPoly01 L ^ 2 = ons_spinDetPoly L 1 0 := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply hinter.mono
    intro x hx
    simp only [Set.mem_setOf_eq, eval_pow, eval_ons_spinPoly01,
      eval_ons_spinDetPoly]
    exact (hsmall x hx).2.1
  have h10poly : ons_spinPoly10 L ^ 2 = ons_spinDetPoly L 0 1 := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply hinter.mono
    intro x hx
    simp only [Set.mem_setOf_eq, eval_pow, eval_ons_spinPoly10,
      eval_ons_spinDetPoly]
    exact (hsmall x hx).2.2.1
  have h00poly : ons_spinPoly00 L ^ 2 = ons_spinDetPoly L 1 1 := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply hinter.mono
    intro x hx
    simp only [Set.mem_setOf_eq, eval_pow, eval_ons_spinPoly00,
      eval_ons_spinDetPoly]
    exact (hsmall x hx).2.2.2
  intro x
  unfold ons_spinKacWardAt
  constructor
  · simpa [← eval_ons_spinPoly11, ← eval_ons_spinDetPoly] using
      congrArg (eval x) h11poly
  constructor
  · simpa [← eval_ons_spinPoly01, ← eval_ons_spinDetPoly] using
      congrArg (eval x) h01poly
  constructor
  · simpa [← eval_ons_spinPoly10, ← eval_ons_spinDetPoly] using
      congrArg (eval x) h10poly
  · simpa [← eval_ons_spinPoly00, ← eval_ons_spinDetPoly] using
      congrArg (eval x) h00poly

theorem ons_spinKacWardIdentities_of_small
    (epsilon : ℕ → ℝ) (hepsilon : ∀ L, 0 < epsilon L)
    (hsmall : ∀ (L : ℕ) (hL : 2 < L),
      letI : Fact (2 < L) := ⟨hL⟩
      ∀ x ∈ Set.Ioo (0 : ℝ) (epsilon L), ons_spinKacWardAt L x)
    (beta : ℝ) : ons_spinKacWardIdentities beta := by
  intro L hL
  letI : Fact (2 < L) := ⟨hL⟩
  have hall := ons_spinKacWardAt_all_of_small L (hepsilon L)
    (hsmall L hL) (Real.tanh beta)
  unfold ons_spinKacWardAt at hall
  simpa [ons_spinDet_eq_spinDetX] using hall

end StatMech.Onsager
