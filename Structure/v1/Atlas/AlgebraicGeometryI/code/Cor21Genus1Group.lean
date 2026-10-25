/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Cor21Genus1Group.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Def.v1.Atlas.AlgebraicGeometryI.code.Cor21Genus1Group
set_option maxHeartbeats 400000


noncomputable section

/-- Predicate witnessing that an affine Weierstrass curve is smooth (elliptic) and of genus 1. -/
structure IsSmooth_Genus1 {F : Type*} [Field F]
    (W : WeierstrassCurve.Affine F) : Prop where
  smooth : W.IsElliptic
  genus_eq_one : W.arithmeticGenus = 1

end
