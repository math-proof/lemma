/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TateCechInfra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.SerreDualityTate.Part3
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.SerreDualityTate
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.SerreDualityAnnihilator
import Theorem.v1.Atlas.AlgebraicGeometryI.code.SerreDualityAnnihilator
import Class.v1.Atlas.AlgebraicGeometryI.code.TateCechInfra


noncomputable section

universe v

namespace TateCechInfra

open SerreDualityTate SerreDualityCurves

open CanonicalSheafCurves RiemannRochCurves SerreDualityP1

open SheafCohCurvesFiniteness CohomologyP1 SheafCohomology

open SerreDualityAnnihilator

variable (k : Type*) [Field k]

/-- Packaging the data needed to apply Tate self-duality machinery to a Čech
cohomology setup on a smooth complete curve, recording the Riemann–Roch
identities for both `E` and the dualized line bundle `K - E`. -/
structure CechSheafData where
  setup : TateDualitySetup.{_, v} k
  [instFD : FiniteDimensional k setup.V]
  curve : SmoothCompleteCurve
  deg : ℤ
  h0_E : ℤ
  h1_EK : ℤ
  hRR_E : h0_E - ↑(Module.finrank k setup.cechH1) = curve.χ (1, deg)
  hRR_EK : ↑(Module.finrank k ↥setup.dual.cechH0) - h1_EK =
            curve.χ (1, curve.degK - deg)

end TateCechInfra
end
