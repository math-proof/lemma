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
import Def.v1.Atlas.EllipticCurves.code.DivisionPolynomials.Part2
open Polynomial
open scoped Polynomial.Bivariate


namespace ShortWeierstrassCurve

variable {R : Type*} [CommRing R] (E : ShortWeierstrassCurve R)

/-- The zeroth division polynomial vanishes, $\psi_0 = 0$. -/
@[simp] lemma divisionPoly_zero : E.divisionPoly 0 = 0 :=
  E.toWeierstrassCurve.ψ_zero

/-- The first division polynomial is $\psi_1 = 1$. -/
@[simp] lemma divisionPoly_one : E.divisionPoly 1 = 1 :=
  E.toWeierstrassCurve.ψ_one

/-- The second division polynomial is $\psi_2$, equal to the Mathlib helper `ψ₂`. -/
@[simp] lemma divisionPoly_two : E.divisionPoly 2 = E.toWeierstrassCurve.ψ₂ :=
  E.toWeierstrassCurve.ψ_two

end ShortWeierstrassCurve
