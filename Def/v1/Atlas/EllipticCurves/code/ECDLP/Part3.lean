/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ECDLP.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.v1.Atlas.EllipticCurves.code.ECDLP


section Example_9_1

variable [Module (ZMod N) G]

/-- Canonical ring hom `ZMod N → ZMod (largestPrimeFactor N)` induced by the divisibility
`lp(N) ∣ N`, used to reduce a generic DLP on `ZMod N` to the prime-order subgroup. -/
noncomputable def projToLargestPrime (N : ℕ) (hN : 1 < N) :
    ZMod N →+* ZMod (largestPrimeFactor N hN) :=
  ZMod.castHom (largestPrimeFactor_dvd N hN) (ZMod (largestPrimeFactor N hN))

/-- Expected-value lower bound used in Corollary 9.10: `∑_{m<M} (1 - m²/(2p))`, which
bounds the expected number of group operations for a Las Vegas DLP algorithm. -/
noncomputable def lasVegasExpectedLB (p M : ℕ) : ℝ :=
  ∑ m ∈ Finset.range M, (1 - (↑m : ℝ) ^ 2 / (2 * ↑p))

/-- Shoup's combinatorial constraint on a Las Vegas DLP work function `w`: for every
`s`, at most `s(s-1)/2` instances `t` are solved by `w t ≤ s` queries. -/
def LasVegasShoupConstraint (w : ZMod p → ℕ) : Prop :=
  ∀ s : ℕ, (Finset.univ.filter (fun t : ZMod p => w t ≤ s)).card ≤ s * (s - 1) / 2

end Example_9_1
