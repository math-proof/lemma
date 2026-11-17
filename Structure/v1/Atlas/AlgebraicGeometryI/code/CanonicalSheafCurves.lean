/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalSheafCurves.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.AlgebraicGeometryI.code.CoherentSheavesCurves.Part2
public import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CoherentSheavesCurves
public import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalBundleProjective
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalBundleGeneral
public import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannRochCurves
public import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalBundleProjective.Part4
public import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalBundleGeneral
public import Theorem.v1.Atlas.AlgebraicGeometryI.code.RiemannRochCurves
public import Theorem.v1.Atlas.AlgebraicGeometryI.code.CanonicalSheafCurves
set_option maxHeartbeats 800000

open RiemannRochCurves


public noncomputable section

namespace CanonicalSheafCurves

/-- For every natural number `g`, there exists a smooth complete curve of genus `g`. -/
structure SmoothCompleteCurve where
  g : ℤ
  χ : ℤ × ℤ →+ ℤ
  degK : ℤ
  hg_nonneg : 0 ≤ g
  hχ_struct : χ (1, 0) = 1 - g
  hχ_sky : χ (0, 1) = 1
  hwf : CurveWitness g

end CanonicalSheafCurves
end
