/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter4/DistinctSums.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic
import Instance.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter4.DistinctSums
set_option maxHeartbeats 400000


namespace HarperIsoperimetric

/-- The vertex boundary of a set $A$ in the hypercube: vertices outside $A$ adjacent
    to some vertex in $A$. -/
def Hypercube.vertexBoundary {k : ℕ} (A : Finset (Hypercube k)) : Finset (Hypercube k) :=
  Finset.univ.filter fun v => v ∉ A ∧ ∃ u ∈ A, Hypercube.Adjacent u v

/-- Harper's vertex-isoperimetric inequality on the hypercube (Theorem 4.6.4):
    any set $A \subseteq \{0,1\}^k$ of size $2^{k-1}$ has vertex boundary at least
    $\binom{k}{\lfloor k/2 \rfloor}$. -/

end HarperIsoperimetric

namespace DubroffFoxXu

open Finset BigOperators

/-- Weighted sum $\sum_{i : \varepsilon_i = \mathtt{true}} x_i$ selecting coordinates of $x$
    indicated by the Boolean string $\varepsilon$. -/
def weightedSum {k : ℕ} (x : Fin k → ℕ) (ε : Fin k → Bool) : ℕ :=
  ∑ i : Fin k, if ε i then x i else 0

/-- Coordinatewise Boolean complement of $\varepsilon \in \{0,1\}^k$. -/
def boolCompl {k : ℕ} (ε : Fin k → Bool) : Fin k → Bool := fun i => !ε i

/-- The subset of $\mathrm{Fin}\, k$ on which the Boolean function $\varepsilon$ is true. -/
def boolToFinset {k : ℕ} (ε : Fin k → Bool) : Finset (Fin k) :=
  Finset.univ.filter (fun i => ε i = true)

/-- Variant of `HasDistinctSubsetSums` for tuples $x : \mathrm{Fin}\, k \to \mathbb{N}$:
    the map sending a subset $T$ to $\sum_{i \in T} x_i$ is injective. -/
def HasDistinctSubsetSumsFin {k : ℕ} (x : Fin k → ℕ) : Prop :=
  Function.Injective (fun T : Finset (Fin k) => ∑ i ∈ T, x i)

/-- Vertex boundary of $A$ in the hypercube $\{0,1\}^k$, formulated via differing in
    exactly one coordinate from some vertex in $A$. -/
def cubeBoundary {k : ℕ} (A : Finset (Fin k → Bool)) : Finset (Fin k → Bool) :=
  Finset.univ.filter (fun v => v ∉ A ∧
    ∃ u ∈ A, ∃ i : Fin k, (∀ j : Fin k, j ≠ i → v j = u j) ∧ v i ≠ u i)

/-- Sign encoding of a Boolean: $\mathtt{true} \mapsto +1$, $\mathtt{false} \mapsto -1$. -/
def boolSign (b : Bool) : ℤ := if b then 1 else -1

end DubroffFoxXu
