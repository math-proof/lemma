/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/NijenhuisGoals.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
import Structure.v1.Atlas.GeometryOfManifolds.code.NijenhuisGoals
set_option autoImplicit false
set_option maxHeartbeats 800000

open DifferentialFormSpace


/-- The Nijenhuis tensor on a manifold: $N_J(U, V) = [JU, JV] - J[U, JV] - J[JU, V] - [U, V]$. -/
noncomputable def nijenhuisTensorMfd (Jstr : ACSOnMfd I M) (U V : ∀ x : M, TangentSpace I x)
    (x : M) : TangentSpace I x :=
  VectorField.mlieBracket I (fun y => Jstr.J y (U y)) (fun y => Jstr.J y (V y)) x
    - Jstr.J x (VectorField.mlieBracket I U (fun y => Jstr.J y (V y)) x)
    - Jstr.J x (VectorField.mlieBracket I (fun y => Jstr.J y (U y)) V x)
    - VectorField.mlieBracket I U V x

