/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochRiemannForm.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicGeometryI.code.RiemannRochEulerCurves
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannRochEulerCurves
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.SheafCohCurvesFiniteness
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannFormRR
import Instance.v1.Atlas.AlgebraicGeometryI.code.SheafCohCurvesFiniteness
import Def.v1.Atlas.AlgebraicGeometryI.code.RiemannFormRR
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

end RiemannRochRiemannForm
end
