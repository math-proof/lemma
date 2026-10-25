/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProjectiveSpaceDef.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Projectivization.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.ProjectiveSpaceDef
open scoped LinearAlgebra.Projectivization


namespace ProjectiveSpace

variable {k : Type*} [DivisionRing k] {n : ℕ}

/-- Projective `n`-space `P^n(k)` is nonempty. -/
instance : Nonempty (ProjectiveSpace k n) := by
  have : Nontrivial (Fin (n + 1) → k) := Pi.nontrivial
  exact inferInstanceAs (Nonempty (Projectivization k (Fin (n + 1) → k)))

end ProjectiveSpace
