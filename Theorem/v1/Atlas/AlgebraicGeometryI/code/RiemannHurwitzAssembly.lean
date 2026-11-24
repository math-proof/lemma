module
public import Theorem.v1.Atlas.AlgebraicGeometryI.code.RiemannHurwitz
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannHurwitz
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalSheafCurves
public import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalSheafCurves.Part2
public import Structure.v1.Atlas.AlgebraicGeometryI.code.RiemannHurwitzAssembly


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzAssembly.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

open CanonicalSheafCurves

namespace RiemannHurwitzAssembly

namespace CurveCovering

example : (2 : ℤ) * 1 - 2 = 2 * (2 * 0 - 2) + 4 := by norm_num

example : (2 : ℤ) * 2 - 2 = 2 * (2 * 0 - 2) + 6 := by norm_num

example : (2 : ℤ) * 3 - 2 = 2 * (2 * 2 - 2) + 0 := by norm_num

example : (2 : ℤ) * 1 - 2 = 3 * (2 * 0 - 2) + 6 := by norm_num

end CurveCovering
end RiemannHurwitzAssembly
end
