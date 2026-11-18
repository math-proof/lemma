module

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Divisors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

public import Mathlib
public import Def.v1.Atlas.ArithmeticGeometry.code.DegreePullback
public import Def.v1.Atlas.ArithmeticGeometry.code.RationalLineCriterion
public import Def.v1.Atlas.ArithmeticGeometry.code.Divisors.Part5
public section
attribute [instance] ClosedPointRes.residueFieldField ClosedPointRes.residueFieldAlgebra
    ClosedPointRes.finiteDimensional

namespace ClosedPoint

variable {G : Type*} {C : Type*} [Group G] [MulAction G C]

class CurveWithOrd (C : Type*) (F : Type*) [Field F] where
  ord : C → Fˣ → ℤ
  ord_mul : ∀ (P : C) (f g : Fˣ), ord P (f * g) = ord P f + ord P g
  ord_add : ∀ (P : C) (f g : Fˣ) (hfg : (f : F) + (g : F) ≠ 0),
    ord P (Units.mk0 ((f : F) + (g : F)) hfg) ≥ min (ord P f) (ord P g)
  uniformizer_exists : ∀ (P : C), ∃ (π : Fˣ), ord P π = 1

class FunctionFieldCurve (C : Type*) (F : Type*) [Field F]
    extends CurveWithOrd C F where
  isCoordRingElem : Fˣ → Prop
  fraction_rep : ∀ (f : Fˣ), ∃ (g h : Fˣ), isCoordRingElem g ∧ isCoordRingElem h ∧
    f = g * h⁻¹
  ord_nonneg_of_coordRingElem : ∀ (f : Fˣ), isCoordRingElem f →
    ∀ (P : C), 0 ≤ CurveWithOrd.ord (F := F) P f
  zeroLocus_finite : ∀ (f : Fˣ), isCoordRingElem f →
    Set.Finite {P : C | 0 < CurveWithOrd.ord (F := F) P f}

end ClosedPoint
