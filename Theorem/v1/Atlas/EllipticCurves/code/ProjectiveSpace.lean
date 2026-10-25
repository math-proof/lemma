/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ProjectiveSpace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Projectivization.Basic
import Abbrev.v1.Atlas.EllipticCurves.code.ProjectiveSpace.Part2
open scoped LinearAlgebra.Projectivization


noncomputable section

namespace ProjectiveSpace

variable (n : ℕ) (k : Type*) [Field k]

example : Nonempty (Plane k) := inferInstance


example : Nonempty (Line k) := inferInstance

end ProjectiveSpace
end
