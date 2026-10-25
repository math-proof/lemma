/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ProjectiveSpace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Projectivization.Basic
open scoped LinearAlgebra.Projectivization


noncomputable section

namespace ProjectiveSpace

variable (n : ℕ) (k : Type*) [Field k]

/-- $n$-dimensional projective space $\mathbb{P}^n(k)$ over $k$, realised as the projectivization
of $k^{n+1}$. -/
abbrev Space : Type _ := Projectivization k (Fin (n + 1) → k)

end ProjectiveSpace
end
