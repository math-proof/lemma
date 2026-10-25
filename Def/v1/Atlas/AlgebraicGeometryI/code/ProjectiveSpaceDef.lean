/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProjectiveSpaceDef.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Projectivization.Basic
open scoped LinearAlgebra.Projectivization


/-- Projective `n`-space `P^n(k)` as the projectivization of `k^{n+1}`. -/
def ProjectiveSpace (k : Type*) [DivisionRing k] (n : ℕ) : Type _ :=
  Projectivization k (Fin (n + 1) → k)

namespace ProjectiveSpace

variable {k : Type*} [DivisionRing k] {n : ℕ}

/-- Form the projective point `[v]` in `P^n(k)` from a nonzero vector `v ∈ k^{n+1}`. -/
def mk (v : Fin (n + 1) → k) (hv : v ≠ 0) : ProjectiveSpace k n :=
  Projectivization.mk k v hv

/-- The quotient map `(k^{n+1} \ {0}) → P^n(k)` sending a nonzero vector to its line. -/
def quotientMap : { v : Fin (n + 1) → k // v ≠ 0 } → ProjectiveSpace k n :=
  Projectivization.mk' k

/-- A choice of representative vector for a projective point. -/
noncomputable def rep (p : ProjectiveSpace k n) : Fin (n + 1) → k :=
  Projectivization.rep p

end ProjectiveSpace
