/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec8Blowup.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Projectivization.Basic
open scoped LinearAlgebra.Projectivization


namespace Lec8Blowup

section Definitions

variable (k : Type*) [Field k] (n : ℕ)

/-- The defining equations `x_i y_j = x_j y_i` for the blowup of
affine space at the origin (Lec 8/9, Def 20). -/
def BlowupEquations (x y : Fin n → k) : Prop :=
  ∀ i j : Fin n, x i * y j = x j * y i

/-- The blowup of `𝔸ⁿ` at the origin, as the incidence subset of
`𝔸ⁿ × ℙⁿ⁻¹` consisting of pairs `(x, ℓ)` with `x ∈ ℓ`
(Lec 8/9, Def 20). -/
def BlowupAffineOrigin : Set ((Fin n → k) × ℙ k (Fin n → k)) :=
  {p | (p.1 : Fin n → k) ∈ p.2.submodule}

/-- Projection from the blowup `Bl₀(𝔸ⁿ)` to `𝔸ⁿ` (Lec 8/9, Def 20). -/
def blowupProjection (p : BlowupAffineOrigin k n) : Fin n → k :=
  p.1.1

end Definitions
end Lec8Blowup
