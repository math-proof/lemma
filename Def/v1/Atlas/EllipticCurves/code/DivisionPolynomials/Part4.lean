/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Polynomial.Wronskian
import Mathlib.FieldTheory.SeparableDegree
import Def.v1.Atlas.EllipticCurves.code.IsogenyKernels.Part4
import Lemma.Complex.Atlas.v1.EllipticCurves.code.IsogenyKernels
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Isogenies
import Lemma.Complex.Atlas.v1.EllipticCurves.code.TorsionEndomorphism
import Def.v1.Atlas.EllipticCurves.code.Isogenies.Part13
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Lemma53
import Def.v1.Atlas.EllipticCurves.code.TorsionEndomorphism.Part3
import Structure.v1.Atlas.EllipticCurves.code.DivisionPolynomials.Part2
open Polynomial
open scoped Polynomial.Bivariate


namespace ShortWeierstrassCurve

variable {R : Type*} [CommRing R] (E : ShortWeierstrassCurve R)

namespace ShortWeierstrassCurve

variable {F : Type*} [Field F] [DecidableEq F] (E : ShortWeierstrassCurve F)

namespace VeluDeg2Data

variable {E : ShortWeierstrassCurve k} (d : VeluDeg2Data E)

/-- Vélu parameter $t = 3 x_0^2 + A$. -/
def t : k := 3 * d.x₀ ^ 2 + E.A

/-- Vélu parameter $w = x_0 t = x_0 (3 x_0^2 + A)$. -/
def w : k := d.x₀ * d.t

/-- Vélu image parameter $A' = A - 5 t$ for the codomain curve. -/
def A' : k := E.A - 5 * d.t

/-- Vélu image parameter $B' = B - 7 w$ for the codomain curve. -/
def B' : k := E.B - 7 * d.w

/-- The image curve $E' : y^2 = x^3 + A' x + B'$ of the Vélu degree-$2$ isogeny. -/
def imageCurve : ShortWeierstrassCurve k := ⟨d.A', d.B'⟩

/-- Numerator of the $x$-coordinate component $\phi_x(x) = x^2 - x_0 x + t$. -/
def phi_x_numer (x : k) : k := x ^ 2 - d.x₀ * x + d.t

/-- Denominator of the $x$-coordinate component $\phi_x$, namely $x - x_0$. -/
def phi_x_denom (x : k) : k := x - d.x₀

/-- Factor appearing in the $y$-coordinate numerator: $(x - x_0)^2 - t$. -/
def phi_y_numer_factor (x : k) : k := (x - d.x₀) ^ 2 - d.t

/-- Denominator of the $y$-coordinate component: $(x - x_0)^2$. -/
def phi_y_denom (x : k) : k := (x - d.x₀) ^ 2

end VeluDeg2Data
end ShortWeierstrassCurve
end ShortWeierstrassCurve
