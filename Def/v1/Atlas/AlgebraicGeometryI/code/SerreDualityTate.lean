module
public import Def.v1.Atlas.AlgebraicGeometryI.code.SerreDualityLinear.Part4
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.SerreDualityLinear
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.SerreDualityCurves
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.ResidueSum
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.SheafCohCurvesFiniteness
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalSheafCurves
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.SerreDualityGeneral
public import Def.v1.Atlas.AlgebraicGeometryI.code.SerreDualityCurves.Part2
public import Def.v1.Atlas.AlgebraicGeometryI.code.ResidueSum
public import Instance.v1.Atlas.AlgebraicGeometryI.code.SheafCohCurvesFiniteness
public import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalSheafCurves.Part2
public import Structure.v1.Atlas.AlgebraicGeometryI.code.SerreDualityTate


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityTate.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
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

/-- The Čech `H⁰` of the setup: the intersection `V₁ ∩ V₂`. -/
def cechH0 : Submodule k S.V := S.V₁ ⊓ S.V₂

/-- The Čech `H¹` of the setup: the quotient `V / (V₁ + V₂)`. -/
def cechH1 : Type _ := S.V ⧸ (S.V₁ ⊔ S.V₂)

end TateDualitySetup
end CechSetup
end SerreDualityTate
end
