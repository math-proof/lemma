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
import Structure.v1.Atlas.EllipticCurves.code.DivisionPolynomials
open Polynomial
open scoped Polynomial.Bivariate


namespace ShortWeierstrassCurve

variable {R : Type*} [CommRing R] (E : ShortWeierstrassCurve R)

/-- The underlying Mathlib `WeierstrassCurve` of a short Weierstrass curve, with
$a_1 = a_2 = a_3 = 0$, $a_4 = A$, $a_6 = B$. -/
noncomputable def toWeierstrassCurve : WeierstrassCurve R :=
  ⟨0, 0, 0, E.A, E.B⟩

end ShortWeierstrassCurve
