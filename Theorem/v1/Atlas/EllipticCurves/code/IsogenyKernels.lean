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
import Def.v1.Atlas.EllipticCurves.code.IsogenyKernels
open Polynomial

variable {E : ShortWeierstrassCurve k}


namespace VeluDeg2Data

variable (d : VeluDeg2Data E)

/-- The $A$-coefficient of the Vélu degree-2 image curve unfolds to $A'$. -/
@[simp] lemma imageCurve_A : d.imageCurve.A = d.A' := rfl

/-- The $B$-coefficient of the Vélu degree-2 image curve unfolds to $B'$. -/
@[simp] lemma imageCurve_B : d.imageCurve.B = d.B' := rfl

end VeluDeg2Data
