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

/-- The projective point $[v_0 : \cdots : v_n] \in \mathbb{P}^n(k)$ associated to a nonzero
vector $v \in k^{n+1}$. -/
def mk (v : Fin (n + 1) → k) (hv : v ≠ 0) : Space n k :=
  Projectivization.mk k v hv

/-- A choice of homogeneous coordinates representing a projective point. -/
def coord (P : Space n k) : Fin (n + 1) → k := P.rep

/-- The projective plane $\mathbb{P}^2(k)$. -/
abbrev Plane : Type _ := Space 2 k

/-- The projective line $\mathbb{P}^1(k)$. -/
abbrev Line : Type _ := Space 1 k


example : Nonempty (Plane k) := inferInstance


example : Nonempty (Line k) := inferInstance

end ProjectiveSpace

end
