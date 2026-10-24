/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter11/GraphContainers.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open SimpleGraph Finset

namespace GraphContainers

/-- The average degree of a finite simple graph, $\bar d(G) = 2|E(G)|/|V(G)|$. -/
noncomputable def avgDegree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  2 * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)

/-- The partial binomial sum $\sum_{i=0}^{k} \binom{n}{i}$, bounding the number of subsets
of an $n$-element set of size at most $k$. -/
def binomialSum (n k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (k + 1), n.choose i

/-- **Container algorithm (fingerprint version, Theorem 11.2.3).** For every $c > 0$ there
exists $0 < \delta < 1$ such that for every graph $G$ with $\Delta(G) \leq c \, \bar d(G)$
there is a function `container` mapping each small "fingerprint" $S$ to a vertex set with
$|container(S)| \leq (1 - \delta) |V|$, and every independent set $I$ has a fingerprint
$S \subseteq I$ of size $\leq 2\delta |V|/\bar d(G)$ with $I \subseteq container(S)$. -/
end GraphContainers
