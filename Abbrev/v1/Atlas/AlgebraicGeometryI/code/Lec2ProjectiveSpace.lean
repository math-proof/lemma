/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec2ProjectiveSpace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Topology.Order
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Topology.Constructions
set_option maxHeartbeats 800000

open scoped LinearAlgebra.Projectivization


noncomputable section

namespace Formalization

/-- Projective `n`-space over `k`, identified with the projectivization of `k^{n+1}`. -/
abbrev ProjectiveSpace (k : Type*) [Field k] (n : ℕ) :=
  Projectivization k (Fin (n + 1) → k)

/-- The punctured affine space `A^{n+1} \ {0}` over `k`, used as the domain of the quotient map
defining `P^n`. -/
abbrev PuncturedAffineSpace (k : Type*) [Field k] (n : ℕ) :=
  { v : Fin (n + 1) → k // v ≠ 0 }

end Formalization
end
