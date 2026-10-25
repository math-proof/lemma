/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6/HypergraphColoring.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Compactness.Compact
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
set_option maxHeartbeats 800000

open Set Topology


namespace HypergraphColoring

variable {V : Type*}

/-- Symmetric LLL applied to hypergraph 2-coloring on a finite vertex set `X`: if each edge has
size $\ge k$ and intersects at most $d$ other edges, and $e \cdot 2^{1-k} (d+1) \le 1$, then a
random uniform coloring avoids all monochromatic edges contained in `X` with positive
probability. Provides the LLL input to the compactness step of Theorem 6.2.1. -/
def goodColorings (edges : Set (Finset V)) (X : Finset V) : Set (V → Bool) :=
  {c | ∀ e ∈ edges, (↑e : Set V) ⊆ ↑X →
    ¬(∀ v ∈ e, c v = true) ∧ ¬(∀ v ∈ e, c v = false)}

/-- Theorem 6.2.6 (infinite-vertex version of Theorem 6.2.1): if each edge has size $\ge k$,
intersects at most $d$ other edges, and the LLL bound $e \cdot 2^{1-k} (d+1) \le 1$ holds, then
the (possibly infinite) hypergraph admits a proper 2-coloring. Combines the finite-case LLL with
a compactness argument. -/
def IsRegular (edges : Set (Finset V)) (k : ℕ) : Prop :=
  ∀ v : V, Set.ncard {e ∈ edges | v ∈ e} = k

end HypergraphColoring
