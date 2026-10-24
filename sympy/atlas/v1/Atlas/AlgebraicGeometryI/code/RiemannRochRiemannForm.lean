/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochRiemannForm.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.RiemannRochEulerCurves
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannRochEulerCurves
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.SheafCohCurvesFiniteness
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannFormRR
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.SheafCohCurvesFiniteness
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.RiemannFormRR

open CanonicalSheafCurves RiemannRochEulerCurves RiemannFormRR
open SheafCohCurvesFiniteness

noncomputable section

namespace RiemannRochRiemannForm

/-- Bundle of Serre-duality data for a sheaf on a smooth complete curve `C`
of class `(r, d)`: nonnegative integers `h0`, `h1` with `χ = h0 − h1` plus
an isomorphism `h1 = h0_dual` exhibiting Serre duality. -/
structure SerreDualityCurve (C : SmoothCompleteCurve) (r d : ℤ) where
  h0 : ℤ
  h1 : ℤ
  h0_dual : ℤ
  chi_decomp : C.χ (r, d) = h0 - h1
  serre_dual : h1 = h0_dual
  h0_nonneg : h0 ≥ 0
  h1_nonneg : h1 ≥ 0

/-- The Serre dual class of `(r, d)`: `(r, r·deg K − d)`. -/
def serreDualClass (C : SmoothCompleteCurve) (r d : ℤ) : ℤ × ℤ :=
  (r, r * C.degK - d)

/-- Smart constructor for `SerreDualityCurve` from raw data. -/
def mkSerreDualityCurve (C : SmoothCompleteCurve) (r d : ℤ)
    (h0 h1 : ℤ) (h0_dual : ℤ)
    (hchi : C.χ (r, d) = h0 - h1)
    (hsd : h1 = h0_dual)
    (hh0 : h0 ≥ 0) (hh1 : h1 ≥ 0) :
    SerreDualityCurve C r d :=
  { h0 := h0
    h1 := h1
    h0_dual := h0_dual
    chi_decomp := hchi
    serre_dual := hsd
    h0_nonneg := hh0
    h1_nonneg := hh1
    }
