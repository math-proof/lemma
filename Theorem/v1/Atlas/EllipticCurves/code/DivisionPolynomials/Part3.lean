module
public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.RingTheory.Polynomial.Wronskian
public import Mathlib.FieldTheory.SeparableDegree
public import Def.v1.Atlas.EllipticCurves.code.IsogenyKernels.Part4
public import Theorem.Complex.Atlas.v1.EllipticCurves.code.IsogenyKernels
public import Theorem.Complex.Atlas.v1.EllipticCurves.code.Isogenies
public import Theorem.Complex.Atlas.v1.EllipticCurves.code.TorsionEndomorphism
public import Def.v1.Atlas.EllipticCurves.code.Isogenies.Part13
public import Theorem.Complex.Atlas.v1.EllipticCurves.code.Lemma53
public import Def.v1.Atlas.EllipticCurves.code.TorsionEndomorphism.Part3
public import Def.v1.Atlas.EllipticCurves.code.DivisionPolynomials.Part3
open Polynomial
open scoped Polynomial.Bivariate


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace ShortWeierstrassCurve

variable {R : Type*} [CommRing R] (E : ShortWeierstrassCurve R)

namespace ShortWeierstrassCurve

variable {F : Type*} [Field F] [DecidableEq F] (E : ShortWeierstrassCurve F)

omit [DecidableEq F] in
/-- Base case: $\psi_1$ evaluates to $1$ at any point. -/
@[simp] lemma evalDivisionPoly_one (x₀ y₀ : F) :
    E.evalDivisionPoly 1 x₀ y₀ = 1 := by
  simp [evalDivisionPoly, divisionPoly, Polynomial.evalBivariate]

omit [DecidableEq F] in
/-- Base case: $\phi_1(x_0, y_0) = x_0$. -/
@[simp] lemma evalPhiPoly_one (x₀ y₀ : F) :
    E.evalPhiPoly 1 x₀ y₀ = x₀ := by
  simp [evalPhiPoly, phiPoly, Polynomial.evalBivariate, eval_C, eval_X]

end ShortWeierstrassCurve
end ShortWeierstrassCurve
