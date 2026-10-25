/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Instance.v1.Atlas.EllipticCurves.code.IntegerFactorization
open Nat Real Filter Asymptotics Finset


noncomputable section

/-- The count `Ψ(x, y)`: the number of `⌊y⌋`-smooth positive integers up to `⌊x⌋`. -/
def smoothCount (x y : ℝ) : ℕ :=
  (Nat.smoothNumbersUpTo (⌊x⌋₊) (⌊y⌋₊ + 1)).card

/-- The Canfield–Erdős–Pomerance filter on `(u, x)`: pairs going to infinity
constrained by `u < (1 - ε) · log x / log log x`. Used to state the CEP asymptotic. -/
def cepFilter (ε : ℝ) : Filter (ℝ × ℝ) :=
  (atTop ×ˢ atTop) ⊓
    Filter.principal {p : ℝ × ℝ | p.1 < (1 - ε) * Real.log p.2 / Real.log (Real.log p.2)}

/-- Canfield–Erdős–Pomerance theorem: in the range `u < (1 - ε) log x / log log x`,
`log(Ψ(x, x^{1/u}) / x) + u log u = o(u log u)`, i.e. the density of smooth
numbers is governed by Dickman's function. -/

end

/-- The factor base of bound `B`: the finset of primes `q ≤ B`. -/
def factorBase (B : ℕ) : Finset ℕ :=
  Nat.primesBelow (B + 1)

/-- The discrete logarithm of `β ∈ G` to base `g` (where `g` generates the cyclic
group of order `n`), valued in `ZMod n`. Built by transporting through the
isomorphism `G ≃ Multiplicative (ZMod n)` induced by the generator. -/
noncomputable def dlog (β : G) : ZMod n :=
  Multiplicative.toAdd ((zmodMulEquivOfGenerator hg hn).symm β)

