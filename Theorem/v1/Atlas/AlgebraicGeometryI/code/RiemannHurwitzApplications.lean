/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzApplications.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicGeometryI.code.RiemannHurwitzDegree
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannHurwitzDegree
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.NormalExtension
import Def.v1.Atlas.AlgebraicGeometryI.code.NormalExtension
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Ideal.Height
import Def.v1.Atlas.AlgebraicGeometryI.code.RiemannHurwitzApplications


noncomputable section

open RiemannHurwitzFormula CanonicalSheafCurves RiemannHurwitzDegree

namespace RiemannHurwitzApplications

section GenusBounds

example : (2 : ℤ) * 4 - 2 = 3 * (2 * 2 - 2) + 0 := by norm_num

example : (2 : ℤ) * 0 - 2 = 2 * (2 * 0 - 2) + 2 := by norm_num

example : (2 : ℤ) * 1 - 2 = 2 * (2 * 1 - 2) + 0 := by norm_num

example : (2 : ℤ) * 3 - 2 = 2 * (2 * 2 - 2) + 0 := by norm_num

example : (2 : ℤ) * 11 - 2 = 5 * (2 * 3 - 2) + 0 := by norm_num

example : (mkCurve 0).degK = -2 := by norm_num [mkCurve]

example : (2 : ℤ) * 0 - 2 = 1 * (2 * 0 - 2) + 0 := by norm_num

end GenusBounds
end RiemannHurwitzApplications
end
