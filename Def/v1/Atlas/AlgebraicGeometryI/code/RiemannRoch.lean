/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRoch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicGeometryI.code.CohomologyP1.Part2
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CohomologyP1
import Mathlib.Tactic
set_option maxHeartbeats 400000

open CohomologyP1


namespace RiemannRoch

variable (k : Type) [Field k]


/-- Dimension of `H^0(ℙ¹, 𝒪(n))` over `k`, via the Čech computation. -/
noncomputable def dimH0 (n : ℤ) : ℕ :=
  Module.finrank k ↥(CechH0 k n)

/-- Dimension of `H^1(ℙ¹, 𝒪(n))` over `k`, via the Čech computation. -/
noncomputable def dimH1 (n : ℤ) : ℕ :=
  Module.finrank k ((ℤ →₀ k) ⧸ (NonNeg k ⊔ AtMost k n))


/-- Genus of a smooth plane curve of degree `d`: `(d - 1)(d - 2) / 2`. -/
def genus (d : ℕ) : ℕ := (d - 1) * (d - 2) / 2


/-- Euler characteristic of `𝒪(n)` on `ℙ¹`: `dim H^0 - dim H^1`. -/
noncomputable def euler_char (n : ℤ) : ℤ :=
  (dimH0 k n : ℤ) - (dimH1 k n : ℤ)

end RiemannRoch
