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
import Theorem.v1.Atlas.ArithmeticGeometry.code.Divisors.Part2
attribute [instance] ClosedPointRes.residueFieldField ClosedPointRes.residueFieldAlgebra
    ClosedPointRes.finiteDimensional


namespace ClosedPoint

variable {G : Type*} {C : Type*} [Group G] [MulAction G C]

namespace CurveWithOrd

variable {C : Type*} {F : Type*} [Field F] [FunctionFieldCurve C F]

noncomputable def principalDivisorHom :
    Fˣ →* Multiplicative (CurveDivisor C) where
  toFun f := Multiplicative.ofAdd (principalDivisor f)
  map_one' := by simp
  map_mul' f g := by
    simp only [principalDivisor_mul]
    rfl

noncomputable def principalDivisors : AddSubgroup (CurveDivisor C) where
  carrier := Set.range (fun f : Fˣ => principalDivisor (C := C) f)
  add_mem' := by
    rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩
    exact ⟨f * g, principalDivisor_mul f g⟩
  zero_mem' := ⟨1, principalDivisor_one⟩
  neg_mem' := by
    rintro _ ⟨f, rfl⟩
    exact ⟨f⁻¹, principalDivisor_inv f⟩

def IsPrincipal (D : CurveDivisor C) : Prop :=
  D ∈ principalDivisors (F := F)

noncomputable def divAddHom : Additive Fˣ →+ CurveDivisor C where
  toFun f := principalDivisor (Additive.toMul f)
  map_zero' := by show principalDivisor (1 : Fˣ) = 0; exact principalDivisor_one
  map_add' f g := by
    show principalDivisor (_ * _) = principalDivisor _ + principalDivisor _
    exact principalDivisor_mul _ _


end CurveWithOrd
end ClosedPoint
