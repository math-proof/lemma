module
public import Theorem.v1.Atlas.AlgebraicGeometryI.code.CechCohomologyIdentification
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.CechCohomologyIdentification
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.GenusConstruction
public import Def.v1.Atlas.AlgebraicGeometryI.code.GenusConstruction.Part2
public import Theorem.v1.Atlas.AlgebraicGeometryI.code.CechSheafDataP1


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CechSheafDataP1.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

universe v

namespace CechSheafDataP1

open SerreDualityTate CanonicalSheafCurves GenusConstruction

open TateCechInfra

variable (k : Type) [Field k]


/-- The smooth complete curve `P¹` constructed from the Čech data. -/
def P1 : SmoothCompleteCurve := P1CurveFromCech k

end CechSheafDataP1
end
