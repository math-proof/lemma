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
import Abbrev.v1.Atlas.ArithmeticGeometry.code.Divisors.Part5
attribute [instance] ClosedPointRes.residueFieldField ClosedPointRes.residueFieldAlgebra
    ClosedPointRes.finiteDimensional


namespace ClosedPoint

variable {G : Type*} {C : Type*} [Group G] [MulAction G C]

namespace CurveWithOrd

variable {C : Type*} {F : Type*} [Field F] [FunctionFieldCurve C F]

namespace FunctionFieldDivisor

variable {F : Type*} [Field F] {k : Type*} [Field k]

noncomputable def coeff (D : FunctionFieldDivisor F k) (P : FunctionFieldPlace F k) : ℤ :=
  D P

noncomputable def divisorSupport (D : FunctionFieldDivisor F k) :
    Finset (FunctionFieldPlace F k) :=
  D.support

end FunctionFieldDivisor

noncomputable section

namespace ArithmeticGeometry

namespace FunctionField_k

variable {k : Type*} [Field k]

variable {F₁ : Type*} {F₂ : Type*} [Field F₁] [Field F₂]

def Morphism.ramificationIndex
    (φ : F₂ →+* F₁)
    (ordP : F₁ˣ → ℤ)
    (tQ : F₂ˣ)
    : ℤ :=
  ordP (Units.map φ.toMonoidHom tQ)


def Morphism.IsUnramifiedAt
    (φ : F₂ →+* F₁)
    (ordP : F₁ˣ → ℤ)
    (tQ : F₂ˣ) : Prop :=
  Morphism.ramificationIndex φ ordP tQ = 1


def Morphism.IsUnramified
    (φ : F₂ →+* F₁)
    (places : Type*)
    (ordAt : places → F₁ˣ → ℤ)
    (uniformizerAt : places → F₂ˣ)
    : Prop :=
  ∀ P : places, Morphism.IsUnramifiedAt φ (ordAt P) (uniformizerAt P)


end FunctionField_k
end ArithmeticGeometry
end
end CurveWithOrd
end ClosedPoint
