/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Theorem.v1.Atlas.AlgebraicGeometryI.code.RiemannHurwitz
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannHurwitz
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalSheafCurves
public import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalSheafCurves.Part2


public noncomputable section

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

end RiemannHurwitzAssembly
end
