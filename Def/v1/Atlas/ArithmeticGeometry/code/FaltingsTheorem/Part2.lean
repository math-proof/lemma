/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/FaltingsTheorem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finite.Defs
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Data.Setoid.Basic
public import Mathlib.RingTheory.Ideal.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Structure.v1.Atlas.ArithmeticGeometry.code.FaltingsTheorem

@[expose] public section

open MvPolynomial


namespace IrreducibleCurveOverQ

def ratPoints (C : IrreducibleCurveOverQ) : Type :=
  projectiveRatPoints C.n C.definingEquations

end IrreducibleCurveOverQ
