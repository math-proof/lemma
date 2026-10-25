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
import Def.v1.Atlas.EllipticCurves.code.DivisionPolynomials
open Polynomial
open scoped Polynomial.Bivariate


namespace ShortWeierstrassCurve

variable {R : Type*} [CommRing R] (E : ShortWeierstrassCurve R)

/-- The first Weierstrass coefficient $a_1$ of a short Weierstrass curve vanishes. -/
@[simp] lemma toWeierstrassCurve_a₁ : E.toWeierstrassCurve.a₁ = 0 := rfl

/-- The second Weierstrass coefficient $a_2$ of a short Weierstrass curve vanishes. -/
@[simp] lemma toWeierstrassCurve_a₂ : E.toWeierstrassCurve.a₂ = 0 := rfl

/-- The third Weierstrass coefficient $a_3$ of a short Weierstrass curve vanishes. -/
@[simp] lemma toWeierstrassCurve_a₃ : E.toWeierstrassCurve.a₃ = 0 := rfl

/-- The fourth Weierstrass coefficient $a_4$ of a short Weierstrass curve equals $A$. -/
@[simp] lemma toWeierstrassCurve_a₄ : E.toWeierstrassCurve.a₄ = E.A := rfl

/-- The sixth Weierstrass coefficient $a_6$ of a short Weierstrass curve equals $B$. -/
@[simp] lemma toWeierstrassCurve_a₆ : E.toWeierstrassCurve.a₆ = E.B := rfl

/-- The auxiliary invariant $b_2 = a_1^2 + 4 a_2$ of a short Weierstrass curve vanishes. -/
@[simp] lemma b₂_eq : E.toWeierstrassCurve.b₂ = 0 := by
  simp [WeierstrassCurve.b₂, toWeierstrassCurve]

/-- The auxiliary invariant $b_4 = 2 a_4 + a_1 a_3$ of a short Weierstrass curve equals $2A$. -/
@[simp] lemma b₄_eq : E.toWeierstrassCurve.b₄ = 2 * E.A := by
  simp [WeierstrassCurve.b₄, toWeierstrassCurve]

/-- The auxiliary invariant $b_6 = a_3^2 + 4 a_6$ of a short Weierstrass curve equals $4B$. -/
@[simp] lemma b₆_eq : E.toWeierstrassCurve.b₆ = 4 * E.B := by
  simp [WeierstrassCurve.b₆, toWeierstrassCurve]

/-- The auxiliary invariant $b_8$ of a short Weierstrass curve equals $-A^2$. -/
@[simp] lemma b₈_eq : E.toWeierstrassCurve.b₈ = -(E.A ^ 2) := by
  simp [WeierstrassCurve.b₈, toWeierstrassCurve]

end ShortWeierstrassCurve
