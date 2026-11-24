module
public import Mathlib
public import Def.v1.Atlas.ArithmeticGeometry.code.DegreePullback
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.DegreePullback
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.RationalLineCriterion
public import Def.v1.Atlas.ArithmeticGeometry.code.RationalLineCriterion
public import Def.v1.Atlas.ArithmeticGeometry.code.Divisors.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Divisors.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

attribute [instance] ClosedPointRes.residueFieldField ClosedPointRes.residueFieldAlgebra
    ClosedPointRes.finiteDimensional


abbrev ClosedPoint (G : Type*) (C : Type*) [Group G] [MulAction G C] :=
  MulAction.orbitRel.Quotient G C

