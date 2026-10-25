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
import Instance.v1.Atlas.ArithmeticGeometry.code.Divisors
attribute [instance] ClosedPointRes.residueFieldField ClosedPointRes.residueFieldAlgebra
    ClosedPointRes.finiteDimensional


namespace CurveDivisor

variable {C : Type*}

def IsDefinedOverK (G : Type*) [Group G] [MulAction G C]
    (D : CurveDivisor C) : Prop :=
  ∀ (σ : G), σ • D = D


end GaloisAction

noncomputable def divZeros (D : CurveDivisor C) : CurveDivisor C := D ⊔ 0

noncomputable def divPoles (D : CurveDivisor C) : CurveDivisor C := (-D) ⊔ 0

