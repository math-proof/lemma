/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Cor21Genus1Group.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Structure.v1.Atlas.AlgebraicGeometryI.code.Cor21Genus1Group
set_option maxHeartbeats 400000


noncomputable section

/-- Corollary 21 (Lec 17): a smooth (elliptic) curve of genus 1 carries a canonical abelian
group structure on its points. -/
@[reducible]
def corollary21_genus1_group {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) (hg1 : IsSmooth_Genus1 W) :
    AddCommGroup W.Point :=
  letI := hg1.smooth; inferInstance

end
