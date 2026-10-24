/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/QExpansions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.EllipticCurves.code.Uniformization
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Uniformization
import Mathlib.NumberTheory.ArithmeticFunction.Misc

noncomputable section

open Complex ArithmeticFunction

namespace ComplexLattice

variable (τ : UpperHalfPlane)

/-- The *nome* `q = e^{2πiτ}` associated to `τ ∈ ℍ`. -/
def nome (τ : UpperHalfPlane) : ℂ :=
  Complex.exp (2 * ↑Real.pi * I * (τ : ℂ))

/-- **Lemma 19.5** (q-expansion of `g₂`). For the lattice associated to
`τ ∈ ℍ`, the Eisenstein-like coefficient `g₂` of its Weierstrass form admits the
q-expansion
`g₂(τ) = (4π⁴/3)·(1 + 240 ∑_{n≥1} σ₃(n) qⁿ)`,
where `σ₃(n)` is the divisor sum `∑_{d|n} d³`. -/
end ComplexLattice
