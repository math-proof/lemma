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
import Def.v1.Atlas.EllipticCurves.code.DivisionPolynomials.Part4
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

/-- Bundled kernel data for the Vélu degree-$2$ isogeny: the kernel point is on $E$, the
denominators vanish at it, are nonzero elsewhere, and the kernel has order $2$. -/
structure VeluDeg2Kernel (E : ShortWeierstrassCurve F) (d : VeluDeg2Data E) where
  kernel_point_on_E : (0 : F) ^ 2 = d.x₀ ^ 3 + E.A * d.x₀ + E.B
  kernel_point_maps_to_zero : d.phi_x_denom d.x₀ = 0
  nonkernel_welldefined : ∀ x : F, x ≠ d.x₀ → d.phi_x_denom x ≠ 0
  kernel_order : ({(d.x₀, (0 : F))} : Finset (F × F)).card + 1 = 2

end FieldTheorems
end VeluDeg2Data
end ShortWeierstrassCurve
end ShortWeierstrassCurve
