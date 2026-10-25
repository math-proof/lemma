/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/IsometryGroups.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.Coxeter.Length
set_option linter.unusedSectionVars false


namespace IsometryBuilding

variable {k : Type*} [CommRing k] {V : Type*} [AddCommGroup V] [Module k V]


/-- A subspace $W \le V$ is **totally isotropic** for the bilinear form $B$ if $B(v,w) = 0$
for all $v, w \in W$. -/
def IsotropicSubspace (B : LinearMap.BilinForm k V) (W : Submodule k V) : Prop :=
  ∀ v ∈ W, ∀ w ∈ W, B v w = 0


end IsometryBuilding
