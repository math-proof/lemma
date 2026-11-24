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
public import Theorem.v1.Atlas.EllipticCurves.code.DivisionPolynomials
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

/-- The $n$-th division polynomial $\psi_n \in R[X][Y]$ of a short Weierstrass curve, as a
bivariate polynomial. Computed from Mathlib's `WeierstrassCurve.ψ`. -/
noncomputable def divisionPoly (n : ℤ) : R[X][Y] :=
  E.toWeierstrassCurve.ψ n

end ShortWeierstrassCurve
