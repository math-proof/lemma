module
public import Theorem.v1.Atlas.AlgebraicGeometryI.code.RiemannRochEulerCurves
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannRochEulerCurves
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.SheafCohCurvesFiniteness
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannFormRR
public import Instance.v1.Atlas.AlgebraicGeometryI.code.SheafCohCurvesFiniteness
public import Def.v1.Atlas.AlgebraicGeometryI.code.RiemannFormRR
public import Structure.v1.Atlas.AlgebraicGeometryI.code.RiemannRochRiemannForm
open CanonicalSheafCurves RiemannRochEulerCurves RiemannFormRR
open SheafCohCurvesFiniteness


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochRiemannForm.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

namespace RiemannRochRiemannForm

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

end RiemannRochRiemannForm
end
