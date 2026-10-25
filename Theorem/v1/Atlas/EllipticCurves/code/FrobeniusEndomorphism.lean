/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FrobeniusEndomorphism.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.CharP.Frobenius
import Structure.v1.Atlas.EllipticCurves.code.FrobeniusEndomorphism
open Polynomial

universe u


namespace FrobeniusEndomorphism

variable {F : Type u} [Field F]

variable {W : WeierstrassCurve.Affine F} {φ : F →+* F}

/-- A coefficient-fixing ring homomorphism commutes with two-variable evaluation of the
defining polynomial of $W$: $f_W(\varphi x, \varphi y) = \varphi(f_W(x, y))$. -/
lemma evalEval_polynomial_map (hφ : FixesCoeffs W φ) (x y : F) :
    Polynomial.evalEval (φ x) (φ y) W.polynomial =
    φ (Polynomial.evalEval x y W.polynomial) := by
  simp only [WeierstrassCurve.Affine.polynomial, Polynomial.evalEval,
    map_sub, map_add, map_mul, map_pow, Polynomial.eval_sub, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    hφ.fix_a₁, hφ.fix_a₂, hφ.fix_a₃, hφ.fix_a₄, hφ.fix_a₆]

/-- A coefficient-fixing endomorphism sends solutions of the Weierstrass equation to
solutions: if $W(x, y) = 0$ then $W(\varphi x, \varphi y) = 0$. -/
lemma equation_preserved (hφ : FixesCoeffs W φ) {x y : F}
    (h : W.Equation x y) : W.Equation (φ x) (φ y) := by
  show Polynomial.evalEval (φ x) (φ y) W.polynomial = 0
  rw [evalEval_polynomial_map hφ, h, map_zero]

/-- A coefficient-fixing endomorphism commutes with two-variable evaluation of the
$x$-partial derivative $\partial_x W$ of the defining polynomial. -/
lemma evalEval_polynomialX_map (hφ : FixesCoeffs W φ) (x y : F) :
    Polynomial.evalEval (φ x) (φ y) W.polynomialX =
    φ (Polynomial.evalEval x y W.polynomialX) := by
  simp only [WeierstrassCurve.Affine.polynomialX, Polynomial.evalEval,
    Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_ofNat, map_sub, map_add, map_mul, map_pow,
    hφ.fix_a₁, hφ.fix_a₂, hφ.fix_a₄, map_ofNat]

/-- A coefficient-fixing endomorphism commutes with two-variable evaluation of the
$y$-partial derivative $\partial_y W$ of the defining polynomial. -/
lemma evalEval_polynomialY_map (hφ : FixesCoeffs W φ) (x y : F) :
    Polynomial.evalEval (φ x) (φ y) W.polynomialY =
    φ (Polynomial.evalEval x y W.polynomialY) := by
  simp only [WeierstrassCurve.Affine.polynomialY, Polynomial.evalEval,
    Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_ofNat, map_add, map_mul,
    hφ.fix_a₁, hφ.fix_a₃, map_ofNat]

/-- An injective coefficient-fixing endomorphism preserves nonsingularity: if
$(x, y)$ is a nonsingular point on $W$, so is $(\varphi x, \varphi y)$. -/
lemma nonsingular_preserved (hφ : FixesCoeffs W φ) (hφ_inj : Function.Injective φ)
    {x y : F} (h : W.Nonsingular x y) :
    W.Nonsingular (φ x) (φ y) := by
  obtain ⟨heq, hor⟩ := h
  refine ⟨equation_preserved hφ heq, ?_⟩
  cases hor with
  | inl hX =>
    left
    rw [evalEval_polynomialX_map hφ]
    exact fun h => hX (hφ_inj (by rw [h, map_zero]))
  | inr hY =>
    right
    rw [evalEval_polynomialY_map hφ]
    exact fun h => hY (hφ_inj (by rw [h, map_zero]))

end FrobeniusEndomorphism
