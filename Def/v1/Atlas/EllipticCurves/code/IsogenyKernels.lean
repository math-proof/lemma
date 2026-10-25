/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IsogenyKernels.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Polynomial.Expand
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Polynomial.Wronskian
import Mathlib.Tactic.LinearCombination
import Structure.v1.Atlas.EllipticCurves.code.IsogenyKernels
open Polynomial

variable {E : ShortWeierstrassCurve k}


namespace VeluDeg2Data

variable (d : VeluDeg2Data E)

/-- Vélu's degree-2 parameter $t = 3 x_0^2 + A$ (twice the slope of the tangent
at the kernel point). -/
def t : k := 3 * d.x₀ ^ 2 + E.A

/-- Vélu's degree-2 parameter $w = x_0 \cdot t$. -/
def w : k := d.x₀ * d.t

/-- New $A$-coefficient $A' = A - 5 t$ of the Vélu degree-2 image curve. -/
def A' : k := E.A - 5 * d.t

/-- New $B$-coefficient $B' = B - 7 w$ of the Vélu degree-2 image curve. -/
def B' : k := E.B - 7 * d.w

/-- The *image curve* $E' : y^2 = x^3 + A' x + B'$ produced by Vélu's
degree-2 formula. -/
def imageCurve : ShortWeierstrassCurve k := ⟨d.A', d.B'⟩

end VeluDeg2Data
