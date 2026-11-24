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
public import Structure.v1.Atlas.EllipticCurves.code.DivisionPolynomials.Part4
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

namespace VeluDeg2Data

variable {E : ShortWeierstrassCurve k} (d : VeluDeg2Data E)

section FieldTheorems

variable {F : Type*} [Field F] {E : ShortWeierstrassCurve F} (d : VeluDeg2Data E)

/-- The Vélu degree-$2$ isogeny constructed from a Vélu datum. -/
def velu_deg2_isogeny : VeluDeg2Isogeny E d where
  phi_maps_points := fun x y hcurve => d.velu_phi_maps_points hcurve
  degree_eq_two := d.velu_deg2_degree_eq_two
  is_separable := d.velu_deg2_is_separable
  kernel := d.velu_deg2_kernel

end FieldTheorems
end VeluDeg2Data
end ShortWeierstrassCurve
end ShortWeierstrassCurve
