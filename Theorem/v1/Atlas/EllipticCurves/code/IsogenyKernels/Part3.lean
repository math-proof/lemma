/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IsogenyKernels.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Polynomial.Wronskian
public import Mathlib.Tactic.LinearCombination
public import Def.v1.Atlas.EllipticCurves.code.IsogenyKernels.Part3
open Polynomial

public section

variable {E : ShortWeierstrassCurve k}


namespace VeluOddData

variable (d : VeluOddData E)

/-- The $A$-coefficient of the Vélu odd-degree image curve unfolds to $A'$. -/
@[simp] lemma imageCurve_A : d.imageCurve.A = d.A' := rfl

/-- The $B$-coefficient of the Vélu odd-degree image curve unfolds to $B'$. -/
@[simp] lemma imageCurve_B : d.imageCurve.B = d.B' := rfl

end VeluOddData
