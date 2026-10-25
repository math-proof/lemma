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
import Class.v1.Atlas.ArithmeticGeometry.code.Divisors
attribute [instance] ClosedPointRes.residueFieldField ClosedPointRes.residueFieldAlgebra
    ClosedPointRes.finiteDimensional


namespace ClosedPoint

variable {G : Type*} {C : Type*} [Group G] [MulAction G C]

theorem FunctionFieldCurve.coordRing_finite_support {C : Type*} {F : Type*} [Field F]
    [inst : FunctionFieldCurve C F] (f : Fˣ) (hf : inst.isCoordRingElem f) :
    (Function.support (fun P => CurveWithOrd.ord (C := C) (F := F) P f)).Finite := by
  apply Set.Finite.subset (inst.zeroLocus_finite f hf)
  intro P hP
  simp only [Set.mem_setOf_eq, Function.mem_support] at hP ⊢
  have := inst.ord_nonneg_of_coordRingElem f hf P
  omega

namespace CurveWithOrd

variable {C : Type*} {F : Type*} [Field F] [CurveWithOrd C F]

theorem ord_one (P : C) : ord (F := F) P 1 = 0 := by
  have h := ord_mul (F := F) P 1 1
  simp at h
  linarith

theorem ord_inv (P : C) (f : Fˣ) : ord (F := F) P f⁻¹ = -ord P f := by
  have h := ord_mul (F := F) P f f⁻¹
  simp only [mul_inv_cancel] at h
  rw [ord_one] at h
  linarith

end CurveWithOrd

theorem ord_finite_support {C : Type*} {F : Type*} [Field F] [FunctionFieldCurve C F]
    (f : Fˣ) :
    (Function.support (fun P => CurveWithOrd.ord (C := C) (F := F) P f)).Finite := by

  obtain ⟨g, h, hg, hh, hf⟩ := FunctionFieldCurve.fraction_rep (C := C) (F := F) f

  have hg_fin := FunctionFieldCurve.coordRing_finite_support g hg
  have hh_fin := FunctionFieldCurve.coordRing_finite_support h hh

  apply Set.Finite.subset (hg_fin.union hh_fin)
  intro P hP
  simp only [Function.mem_support, Set.mem_union] at hP ⊢


  by_contra h_contra
  push Not at h_contra
  obtain ⟨hgP, hhP⟩ := h_contra
  apply hP
  rw [hf, CurveWithOrd.ord_mul, CurveWithOrd.ord_inv]
  omega

end ClosedPoint
