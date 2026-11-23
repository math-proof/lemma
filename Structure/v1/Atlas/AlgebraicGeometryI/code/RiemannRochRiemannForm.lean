/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochRiemannForm.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Theorem.v1.Atlas.AlgebraicGeometryI.code.RiemannRochEulerCurves
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannRochEulerCurves
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.SheafCohCurvesFiniteness
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannFormRR
public import Instance.v1.Atlas.AlgebraicGeometryI.code.SheafCohCurvesFiniteness
public import Def.v1.Atlas.AlgebraicGeometryI.code.RiemannFormRR
open CanonicalSheafCurves RiemannRochEulerCurves RiemannFormRR
open SheafCohCurvesFiniteness


public noncomputable section

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

end RiemannRochRiemannForm
end
