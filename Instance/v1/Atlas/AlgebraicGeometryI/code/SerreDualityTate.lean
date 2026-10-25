/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityTate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.SerreDualityLinear.Part4
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.SerreDualityLinear
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.SerreDualityCurves
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.ResidueSum
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.SheafCohCurvesFiniteness
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalSheafCurves
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.SerreDualityGeneral
import Def.v1.Atlas.AlgebraicGeometryI.code.SerreDualityCurves.Part2
import Def.v1.Atlas.AlgebraicGeometryI.code.ResidueSum
import Instance.v1.Atlas.AlgebraicGeometryI.code.SheafCohCurvesFiniteness
import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalSheafCurves.Part2
import Def.v1.Atlas.AlgebraicGeometryI.code.SerreDualityTate


noncomputable section

namespace SerreDualityTate

open CanonicalSheafCurves RiemannRochCurves SerreDualityP1

open SheafCohCurvesFiniteness CohomologyP1 SheafCohomology

open SerreDualityCurves


section CechSetup

variable (k : Type*) [Field k]

attribute [instance] TateDualitySetup.instACG TateDualitySetup.instModule

variable {k}

namespace TateDualitySetup

variable (S : TateDualitySetup k)

/-- `cechH1` is an additive commutative group, inherited from the quotient. -/
instance cechH1.instACG : AddCommGroup S.cechH1 :=
  inferInstanceAs (AddCommGroup (S.V ⧸ (S.V₁ ⊔ S.V₂)))

/-- `cechH1` is a `k`-module, inherited from the quotient. -/
instance cechH1.instModule : Module k S.cechH1 :=
  inferInstanceAs (Module k (S.V ⧸ (S.V₁ ⊔ S.V₂)))

end TateDualitySetup
end CechSetup
end SerreDualityTate
end
