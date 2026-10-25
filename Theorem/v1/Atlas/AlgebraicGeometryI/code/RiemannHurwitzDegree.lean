/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzDegree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicGeometryI.code.RiemannHurwitzFormula
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannHurwitzFormula
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalSheafCurves
import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalSheafCurves.Part2
import Def.v1.Atlas.AlgebraicGeometryI.code.RiemannHurwitzDegree


noncomputable section

open RiemannHurwitzFormula CanonicalSheafCurves

namespace RiemannHurwitzDegree

example : (2 : ℤ) * 1 - 2 = 2 * (2 * 0 - 2) + 4 := by norm_num

example : (2 : ℤ) * 2 - 2 = 2 * (2 * 0 - 2) + 6 := by norm_num

example : (2 : ℤ) * 3 - 2 = 2 * (2 * 0 - 2) + 8 := by norm_num

example : (2 : ℤ) * 1 - 2 = 3 * (2 * 0 - 2) + 6 := by norm_num

example : (2 : ℤ) * 3 - 2 = 4 * (2 * 0 - 2) + 12 := by norm_num

example : (2 : ℤ) * 3 - 2 = 2 * (2 * 2 - 2) + 0 := by norm_num

example : (2 : ℤ) * 4 - 2 = 3 * (2 * 2 - 2) + 0 := by norm_num

end RiemannHurwitzDegree
end
