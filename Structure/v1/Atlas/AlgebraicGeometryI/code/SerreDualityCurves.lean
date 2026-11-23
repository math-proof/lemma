/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityCurves.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalSheafCurves.Part2
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalSheafCurves
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.SheafCohCurvesFiniteness
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.SerreDualityLinear
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.ResidueSum
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.DedekindCurve
public import Instance.v1.Atlas.AlgebraicGeometryI.code.SheafCohCurvesFiniteness
public import Def.v1.Atlas.AlgebraicGeometryI.code.SerreDualityLinear.Part4
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.SerreDualityGeneral
public import Def.v1.Atlas.AlgebraicGeometryI.code.ResidueSum
public import Def.v1.Atlas.AlgebraicGeometryI.code.DedekindCurve
public import Def.v1.Atlas.AlgebraicGeometryI.code.SerreDualityCurves


public noncomputable section

namespace SerreDualityCurves

open CanonicalSheafCurves RiemannRochCurves SerreDualityP1

open SheafCohCurvesFiniteness CohomologyP1 SheafCohomology


section ResidueMap

variable (k : Type*) [Field k]

/-- Numerical model of a locally free sheaf on a curve `C`: tracks rank and degree. -/
@[ext]
structure LocallyFreeSheaf (C : SmoothCompleteCurve) where
  rk : ℕ
  deg : ℤ


end ResidueMap
end SerreDualityCurves
end
