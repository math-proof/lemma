/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/DegreePullback.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib


noncomputable section

open Ideal Module Finset

/-- The degree $[\kappa(\mathfrak{p}) : k]$ of a closed point $\mathfrak{p} \subseteq R$ over the base field $k$, defined as the dimension of the residue field $R/\mathfrak{p}$ as a $k$-vector space. -/
def closedPointDegree (k : Type*) [Field k] (R : Type*) [CommRing R] [Algebra k R]
    (p : Ideal R) : ℕ :=
  Module.finrank k (R ⧸ p)

/-- The degree of the pullback divisor of a prime $\mathfrak{p}$ under the inclusion $R \hookrightarrow S$: the weighted sum $\sum_{\mathfrak{P} \mid \mathfrak{p}} e(\mathfrak{P}/\mathfrak{p}) \cdot \deg(\mathfrak{P})$ over primes of $S$ lying above $\mathfrak{p}$. -/
def pullbackDivisorDegree (k : Type*) [Field k]
    (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra k R]
    (S : Type*) [CommRing S] [IsDedekindDomain S] [Algebra R S] [Algebra k S]
    (p : Ideal R) : ℕ :=
  (primesOverFinset p S).sum fun P =>
    p.ramificationIdx P * closedPointDegree k S P

end
