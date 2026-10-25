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
import Def.v1.Atlas.EllipticCurves.code.DivisionPolynomials.Part7
open Polynomial
open scoped Polynomial.Bivariate


namespace ShortWeierstrassCurve

variable {R : Type*} [CommRing R] (E : ShortWeierstrassCurve R)

namespace ShortWeierstrassCurve

variable {F : Type*} [Field F] [DecidableEq F] (E : ShortWeierstrassCurve F)

section VeluOdd

variable {k : Type*} [Field k]

variable {E : ShortWeierstrassCurve k}

/-- Unfolds $t_Q$ to its defining formula. -/
@[simp] lemma AffinePoint.tQ_val (Q : AffinePoint E) :
    Q.tQ = 3 * Q.x ^ 2 + E.A := rfl

/-- Unfolds $u_Q$ to its defining formula. -/
@[simp] lemma AffinePoint.uQ_val (Q : AffinePoint E) :
    Q.uQ = 2 * Q.y ^ 2 := rfl

/-- Unfolds $w_Q$ to its defining formula $u_Q + t_Q x_Q$. -/
@[simp] lemma AffinePoint.wQ_val (Q : AffinePoint E) :
    Q.wQ = Q.uQ + Q.tQ * Q.x := rfl

end VeluOdd
end ShortWeierstrassCurve
end ShortWeierstrassCurve
