/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/Symp2TangentSpaces.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Class.v1.Atlas.GeometryOfManifolds.code.TangentBundleDFS
import Def.v1.Atlas.GeometryOfManifolds.code.TwoDimDFS.Part3
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.TwoDimDFS
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.AlmostComplexManifolds
import Structure.v1.Atlas.GeometryOfManifolds.code.AlmostComplexManifolds.Part4
import Theorem.v1.Atlas.GeometryOfManifolds.code.Symp2TangentSpaces
set_option autoImplicit false
set_option maxHeartbeats 1600000

open DifferentialFormSpace SymplecticLinearAlgebra


noncomputable section

/-- The $2$-dimensional symplectic model carries a `HasTangentSpaces` instance: the model
manifold is taken to be `Empty` (it serves only as a tangent-space scaffolding), while the
linear-algebra data (standard $J$, $J^2 = -1$, $J$ preserving $\omega$, taming) is provided
by the lemmas above. -/
noncomputable instance symp2HasTangentSpaces :
    HasTangentSpaces Symp2Ω Symp2VF where
  M := Empty
  TangentSpaceAt := Empty.elim
  instACG := fun x => x.elim
  instMod := fun x => x.elim
  instFD := fun x => x.elim
  eval₂ := fun x => x.elim
  eval₂_add := fun x => x.elim
  eval₂_smul := fun x => x.elim
  eval_is_symplectic := fun _ x => x.elim
  liftJ := fun _ => symp2StdJ
  lift_sq_neg := fun _ _ => symp2_lift_sq_neg
  lift_preserves := fun S _ _ u v => symp2_lift_preserves u v S.ω
  lift_taming := fun S _ _ => symp2_lift_taming S


end
