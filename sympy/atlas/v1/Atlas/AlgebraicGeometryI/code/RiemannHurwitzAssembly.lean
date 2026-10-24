/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.RiemannHurwitz
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannHurwitz
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalSheafCurves
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.CanonicalSheafCurves

noncomputable section

open CanonicalSheafCurves

namespace RiemannHurwitzAssembly

/-- A finite morphism of smooth complete curves: source `X`, target `Y`,
degree `n > 0`, and a ramification divisor of nonnegative degree `deg_R`,
together with the canonical-divisor identity `K_X = n · K_Y + R`. -/
structure CurveCovering where
  X : SmoothCompleteCurve
  Y : SmoothCompleteCurve
  n : ℤ
  hn : 0 < n
  deg_R : ℤ
  deg_R_nonneg : 0 ≤ deg_R
  degK_eq : X.degK = n * Y.degK + deg_R

namespace CurveCovering

example : (2 : ℤ) * 1 - 2 = 2 * (2 * 0 - 2) + 4 := by norm_num

example : (2 : ℤ) * 2 - 2 = 2 * (2 * 0 - 2) + 6 := by norm_num

example : (2 : ℤ) * 3 - 2 = 2 * (2 * 2 - 2) + 0 := by norm_num

example : (2 : ℤ) * 1 - 2 = 3 * (2 * 0 - 2) + 6 := by norm_num

end RiemannHurwitzAssembly

end
