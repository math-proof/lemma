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
import Structure.v1.Atlas.EllipticCurves.code.IsogenyKernels.Part2
open Polynomial

variable {E : ShortWeierstrassCurve k}


namespace VeluOddData

variable (d : VeluOddData E)

/-- Aggregated Vélu parameter $t = \sum_Q t_Q$ over the (odd-order) kernel. -/
def t : k := d.pts.sum (fun Q => Q.tQ)

/-- Aggregated Vélu parameter $w = \sum_Q w_Q$ over the (odd-order) kernel. -/
def w : k := d.pts.sum (fun Q => Q.wQ)

/-- New $A$-coefficient $A' = A - 5 t$ of the Vélu odd-degree image curve. -/
def A' : k := E.A - 5 * d.t

/-- New $B$-coefficient $B' = B - 7 w$ of the Vélu odd-degree image curve. -/
def B' : k := E.B - 7 * d.w

/-- The Vélu odd-degree *image curve* $E' : y^2 = x^3 + A' x + B'$. -/
def imageCurve : ShortWeierstrassCurve k := ⟨d.A', d.B'⟩

end VeluOddData
