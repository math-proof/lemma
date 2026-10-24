/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/SiegelWalfisz.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace SiegelWalfisz

open Finset Real

/-- The prime counting function for an arithmetic progression: the number of primes
$p \le N$ with $p \equiv a \pmod{q}$. -/
noncomputable def primeCountingArithProg (N q a : ℕ) : ℕ :=
  (Finset.filter (fun p => Nat.Prime p ∧ p % q = a % q) (Finset.range (N + 1))).card

/-- **Siegel--Walfisz theorem.** For every $A > 0$ there is a constant $c_A > 0$ such that
for all coprime $a, q$, the discrepancy $\Delta_q(N)$ between the number of primes
$\le N$ in the residue class $a \pmod q$ and the expected value $\pi(N)/\varphi(q)$
satisfies $\Delta_q(N) \le c_A N (\log N)^{-A}$. -/
end SiegelWalfisz
