/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ECDLP.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.EllipticCurves.code.ECDLP


section Example_9_1

/-- A triple `(a, b, γ)` tracked by the Pollard-ρ walk for the DLP: scalars
`a, b ∈ ℤ/Nℤ` together with the corresponding group element `γ = a·α + b·β`. -/
@[ext]
structure PollardRhoTriple (N : ℕ) (G : Type*) where
  a : ZMod N
  b : ZMod N
  γ : G

/-- Configuration for Pollard's rho algorithm (Algorithm 9.5): the generator `α`,
the target `β = log_α^{-1} β`, the number `r` of partition classes (with `0 < r`),
the per-class scalar offsets `c`, `d` and group offsets `δ`, and a partition map `h : G → Fin r`. -/
structure PollardRhoConfig (G : Type*) [AddCommGroup G] (N : ℕ) [NeZero N] where
  α : G
  β : G
  r : ℕ
  hr : 0 < r
  c : Fin r → ZMod N
  d : Fin r → ZMod N
  δ : Fin r → G
  h : G → Fin r

end Example_9_1
