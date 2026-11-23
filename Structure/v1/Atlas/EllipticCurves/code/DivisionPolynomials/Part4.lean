/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

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
public import Def.v1.Atlas.EllipticCurves.code.DivisionPolynomials.Part5
public section

open Polynomial
open scoped Polynomial.Bivariate


namespace ShortWeierstrassCurve

variable {R : Type*} [CommRing R] (E : ShortWeierstrassCurve R)

namespace ShortWeierstrassCurve

variable {F : Type*} [Field F] [DecidableEq F] (E : ShortWeierstrassCurve F)

namespace VeluDeg2Data

variable {E : ShortWeierstrassCurve k} (d : VeluDeg2Data E)

section FieldTheorems

variable {F : Type*} [Field F] {E : ShortWeierstrassCurve F} (d : VeluDeg2Data E)

/-- Bundled Vélu degree-$2$ isogeny: a standard-form separable degree-$2$ isogeny together with
its kernel datum. -/
structure VeluDeg2Isogeny (E : ShortWeierstrassCurve F) (d : VeluDeg2Data E) where
  phi_maps_points : ∀ (x y : F), y ^ 2 = x ^ 3 + E.A * x + E.B →
    ((x - d.x₀) ^ 2 - d.t) ^ 2 * y ^ 2 =
      (x - d.x₀) * ((x ^ 2 - d.x₀ * x + d.t) ^ 3 +
        d.A' * (x ^ 2 - d.x₀ * x + d.t) * (x - d.x₀) ^ 2 +
        d.B' * (x - d.x₀) ^ 3)
  degree_eq_two : max (Polynomial.X ^ 2 - Polynomial.C d.x₀ * Polynomial.X +
    Polynomial.C d.t : F[X]).natDegree (Polynomial.X - Polynomial.C d.x₀ : F[X]).natDegree = 2
  is_separable : Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.C d.x₀ *
    Polynomial.X + Polynomial.C d.t : F[X]) * (Polynomial.X - Polynomial.C d.x₀) -
    (Polynomial.X ^ 2 - Polynomial.C d.x₀ * Polynomial.X + Polynomial.C d.t) *
    Polynomial.derivative (Polynomial.X - Polynomial.C d.x₀) ≠ 0
  kernel : VeluDeg2Kernel E d

end FieldTheorems
end VeluDeg2Data
end ShortWeierstrassCurve
end ShortWeierstrassCurve
