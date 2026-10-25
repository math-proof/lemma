/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/FaltingsTheorem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Finite.Defs
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Data.Setoid.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Structure.v1.Atlas.ArithmeticGeometry.code.FaltingsTheorem
open MvPolynomial


namespace IrreducibleCurveOverQ

def ratPoints (C : IrreducibleCurveOverQ) : Type :=
  projectiveRatPoints C.n C.definingEquations

end IrreducibleCurveOverQ
