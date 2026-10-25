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
set_option autoImplicit false
set_option maxHeartbeats 1600000

open DifferentialFormSpace SymplecticLinearAlgebra


noncomputable section

/-- The standard almost-complex structure $J$ on the $2$-dimensional symplectic model:
$J(a, b) = (-b, a)$, modeling multiplication by $i$. -/
def symp2StdJ : Symp2VF → Symp2VF :=
  fun ⟨a, b⟩ => (-b, a)


end
