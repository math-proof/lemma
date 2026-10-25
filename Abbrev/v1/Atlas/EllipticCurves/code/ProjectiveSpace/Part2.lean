/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ProjectiveSpace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Projectivization.Basic
import Def.v1.Atlas.EllipticCurves.code.ProjectiveSpace
open scoped LinearAlgebra.Projectivization


noncomputable section

namespace ProjectiveSpace

variable (n : ℕ) (k : Type*) [Field k]

/-- The projective plane $\mathbb{P}^2(k)$. -/
abbrev Plane : Type _ := Space 2 k

/-- The projective line $\mathbb{P}^1(k)$. -/
abbrev Line : Type _ := Space 1 k


end ProjectiveSpace
end
