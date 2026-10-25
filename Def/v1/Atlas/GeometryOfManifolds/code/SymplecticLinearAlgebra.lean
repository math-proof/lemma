/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SymplecticLinearAlgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticLinearAlgebra
open Module


namespace SymplecticLinearAlgebra

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The symplectic orthogonal $E^\Omega = \{v \in V : \Omega(v, e) = 0 \text{ for all } e \in E\}$. -/
def symplecticOrtho (Ω : LinearMap.BilinForm ℝ V) (E : Submodule ℝ V) : Submodule ℝ V :=
  Ω.orthogonal E

/-- A subspace $E$ is symplectic with respect to $\Omega$ iff $E \cap E^\Omega = \{0\}$
(Definition 4 in the textbook). -/
def IsSymplecticSubspace (Ω : LinearMap.BilinForm ℝ V) (E : Submodule ℝ V) : Prop :=
  E ⊓ symplecticOrtho Ω E = ⊥

/-- A subspace $E$ is Lagrangian iff $E^\Omega = E$, equivalently isotropic and half-dimensional
(Definition 5 in the textbook). -/
def IsLagrangian (Ω : LinearMap.BilinForm ℝ V) (E : Submodule ℝ V) : Prop :=
  symplecticOrtho Ω E = E

end SymplecticLinearAlgebra
