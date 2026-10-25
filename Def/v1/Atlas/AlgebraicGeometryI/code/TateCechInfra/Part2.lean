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
import Structure.v1.Atlas.AlgebraicGeometryI.code.TateCechInfra


noncomputable section

universe v

namespace TateCechInfra

open SerreDualityTate SerreDualityCurves

open CanonicalSheafCurves RiemannRochCurves SerreDualityP1

open SheafCohCurvesFiniteness CohomologyP1 SheafCohomology

open SerreDualityAnnihilator

variable (k : Type*) [Field k]

attribute [instance] CechSheafData.instFD

variable {k}

/-- The dimension of `H¹(E)` as an integer, extracted from the Čech data. -/
def CechSheafData.h1_E (D : CechSheafData k) : ℤ :=
  ↑(Module.finrank k D.setup.cechH1)

/-- The dimension of `H⁰(K - E)` as an integer, extracted from the Čech data. -/
def CechSheafData.h0_EK (D : CechSheafData k) : ℤ :=
  ↑(Module.finrank k ↥D.setup.dual.cechH0)

end TateCechInfra
end
