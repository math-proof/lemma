/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM1/LinearPDEs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Structure.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM1.LinearPDEs.Part2


namespace LinearDifferentialOperator

/-- Action of a linear differential operator on a function:
$(\mathcal{L} u)(x) = \sum_{|\alpha| \le N} a_{\alpha}(x) \, \partial^{\alpha} u(x)$. -/
noncomputable def apply {n N : ℕ} (L : LinearDifferentialOperator n N)
    (u : (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → ℝ :=
  fun x => ∑ α : { α : MultiIndex' n // multiIndexOrder α ≤ N },
    L.coeff α x * multiIndexDeriv α.1 u x

/-- Repackage a linear differential operator as a genuine $\mathbb{R}$-linear map
$\mathcal{L} : C^{\infty}(\mathbb{R}^n) \to C^{\infty}(\mathbb{R}^n)$, given the linearity
of each multi-index derivative supplied via `hlin`. -/
noncomputable def toLinearMap {n N : ℕ} (L : LinearDifferentialOperator n N)
    (hlin : ∀ α : { α : MultiIndex' n // multiIndexOrder α ≤ N },
      ∀ (a b : ℝ) (u v : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ),
        multiIndexDeriv α.1 (a • u + b • v) x =
          a * multiIndexDeriv α.1 u x + b * multiIndexDeriv α.1 v x) :
    ((Fin n → ℝ) → ℝ) →ₗ[ℝ] ((Fin n → ℝ) → ℝ) where
  toFun := L.apply
  map_add' := by
    intro u v
    funext x
    simp only [apply, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    congr 1
    funext α
    have := hlin α 1 1 u v x
    simp only [one_smul, one_mul] at this
    rw [this]
    ring
  map_smul' := by
    intro c u
    funext x
    simp only [apply, RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    congr 1
    funext α
    have := hlin α c 0 u 0 x
    simp only [zero_smul, add_zero, zero_mul, add_zero] at this
    rw [this]
    ring

end LinearDifferentialOperator
