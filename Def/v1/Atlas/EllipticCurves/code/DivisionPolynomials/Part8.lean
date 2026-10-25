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
import Structure.v1.Atlas.EllipticCurves.code.DivisionPolynomials.Part6
open Polynomial
open scoped Polynomial.Bivariate


namespace ShortWeierstrassCurve

variable {R : Type*} [CommRing R] (E : ShortWeierstrassCurve R)

namespace ShortWeierstrassCurve

variable {F : Type*} [Field F] [DecidableEq F] (E : ShortWeierstrassCurve F)

section VeluOdd

variable {k : Type*} [Field k]

variable {E : ShortWeierstrassCurve k}

namespace VeluOddData

variable (d : VeluOddData E)

/-- Vélu sum $t = \sum_Q t_Q$ over the kernel points. -/
def t : k := d.pts.sum (fun Q => Q.tQ)

/-- Vélu sum $w = \sum_Q w_Q$ over the kernel points. -/
def w : k := d.pts.sum (fun Q => Q.wQ)

/-- Vélu image coefficient $A' = A - 5 t$. -/
def A' : k := E.A - 5 * d.t

/-- Vélu image coefficient $B' = B - 7 w$. -/
def B' : k := E.B - 7 * d.w

/-- The image curve $E' : y^2 = x^3 + A' x + B'$ of the odd-degree Vélu isogeny. -/
def imageCurve : ShortWeierstrassCurve k := ⟨d.A', d.B'⟩

end VeluOddData
end VeluOdd
end ShortWeierstrassCurve
end ShortWeierstrassCurve
