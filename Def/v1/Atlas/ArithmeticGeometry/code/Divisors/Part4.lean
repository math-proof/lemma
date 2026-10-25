/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Divisors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.ArithmeticGeometry.code.DegreePullback
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.DegreePullback
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.RationalLineCriterion
import Def.v1.Atlas.ArithmeticGeometry.code.RationalLineCriterion
import Abbrev.v1.Atlas.ArithmeticGeometry.code.Divisors.Part2
attribute [instance] ClosedPointRes.residueFieldField ClosedPointRes.residueFieldAlgebra
    ClosedPointRes.finiteDimensional


namespace ClosedPoint

variable {G : Type*} {C : Type*} [Group G] [MulAction G C]

def mk (P : C) : ClosedPoint G C := ⟦P⟧

def toOrbit (P : ClosedPoint G C) : Set C :=
  MulAction.orbitRel.Quotient.orbit P

noncomputable def degreeClosedPoint (k K : Type*) [Field k] [Field K] [Algebra k K] : ℕ :=
  Module.finrank k K


end ClosedPoint
