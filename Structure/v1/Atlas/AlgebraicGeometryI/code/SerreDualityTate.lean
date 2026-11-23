/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityTate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

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


public noncomputable section

namespace SerreDualityTate

open CanonicalSheafCurves RiemannRochCurves SerreDualityP1

open SheafCohCurvesFiniteness CohomologyP1 SheafCohomology

open SerreDualityCurves


section CechSetup

variable (k : Type*) [Field k]

/-- A Tate-style duality setup: a `k`-vector space `V` together with two
subspaces `V₁`, `V₂` which model a two-cover Čech setup. -/
structure TateDualitySetup where
  V : Type*
  [instACG : AddCommGroup V]
  [instModule : Module k V]
  V₁ : Submodule k V
  V₂ : Submodule k V

end CechSetup
end SerreDualityTate
end
