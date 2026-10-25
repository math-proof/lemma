/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CurveCoveringBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalDivisorDecomposition.Part4
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalDivisorDecomposition
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannHurwitzDegree
import Theorem.v1.Atlas.AlgebraicGeometryI.code.RiemannHurwitzDegree


noncomputable section

open RiemannHurwitzFormula CanonicalSheafCurves RiemannHurwitzDegree

/-- Convert a `CurveCovering` into the abstract `CurveMorphismData` used by the
Riemann–Hurwitz formula, by packaging degree, canonical degrees, and ramification. -/
def CurveCovering.toCurveMorphismData (C : CurveCovering) : CurveMorphismData where
  degree := C.n
  deg_KX := C.X.degK
  deg_KY := C.Y.degK
  deg_R := C.deg_R
  h_deg_R_nonneg := C.deg_R_nonneg
  h_deg_pos := C.h_n_pos

/-- Package a `CurveCovering` as `CurveCoverData`, combining the morphism data with the
source and target curves. -/
def CurveCovering.toCurveCoverData (C : CurveCovering) : CurveCoverData where
  morphism := C.toCurveMorphismData
  source := C.X
  target := C.Y
  h_degK_X := rfl
  h_degK_Y := rfl

end
