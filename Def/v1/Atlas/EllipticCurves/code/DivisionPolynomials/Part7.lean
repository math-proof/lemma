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
public import Structure.v1.Atlas.EllipticCurves.code.DivisionPolynomials.Part5
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

section VeluOdd

variable {k : Type*} [Field k]

variable {E : ShortWeierstrassCurve k}

/-- Vélu parameter $t_Q = 3 x_Q^2 + A$ associated with an affine point $Q$. -/
def AffinePoint.tQ (Q : AffinePoint E) : k := 3 * Q.x ^ 2 + E.A

/-- Vélu parameter $u_Q = 2 y_Q^2$ associated with an affine point $Q$. -/
def AffinePoint.uQ (Q : AffinePoint E) : k := 2 * Q.y ^ 2

/-- Vélu parameter $w_Q = u_Q + t_Q x_Q$ associated with an affine point $Q$. -/
def AffinePoint.wQ (Q : AffinePoint E) : k := Q.uQ + Q.tQ * Q.x

end VeluOdd
end ShortWeierstrassCurve
end ShortWeierstrassCurve
