/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter2/UnbalancingLights.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
open Finset BigOperators

namespace UnbalancingLights

/-- Conversion from booleans to signs $\{-1, +1\}$: `true ↦ 1`, `false ↦ -1`. -/
def boolToSign (b : Bool) : ℤ := if b then 1 else -1

/-- A vector $v : \mathrm{Fin}\,n \to \mathbb{Z}$ is a sign vector if every entry is
$\pm 1$. -/
def IsSignVec {n : ℕ} (v : Fin n → ℤ) : Prop := ∀ i, v i = 1 ∨ v i = -1

/-- A matrix $a : \mathrm{Fin}\,m \times \mathrm{Fin}\,n \to \mathbb{Z}$ is a sign matrix
if every entry is $\pm 1$. -/
def IsSignMatrix {m n : ℕ} (a : Fin m → Fin n → ℤ) : Prop := ∀ i j, a i j = 1 ∨ a i j = -1

/-- Total Rademacher absolute expectation: $\sum_{y \in \{-1,+1\}^n} \left|
\sum_j y_j \right|$, i.e., the (unnormalized) expected absolute value of a
$\pm 1$ random walk of length $n$. -/
def rademacherAbsExpect (n : ℕ) : ℤ :=
  ∑ y : Fin n → Bool, |∑ j : Fin n, boolToSign (y j)|

/-- Coordinate-wise sign flip on Boolean vectors: flip $y_j$ exactly when $a_j = -1$. -/
def signFlip {n : ℕ} (a : Fin n → ℤ) (y : Fin n → Bool) : Fin n → Bool :=
  fun j => decide (a j = -1) ^^ y j

/-- The sign flip operation is its own inverse. -/
lemma signFlip_involutive {n : ℕ} (a : Fin n → ℤ) :
    Function.Involutive (signFlip a) := by
  intro y; ext j; simp [signFlip]

/-- The sign-flip operation packaged as an `Equiv` on Boolean vectors, used to
relabel sums over $\{-1, +1\}^n$. -/
def signFlipEquiv {n : ℕ} (a : Fin n → ℤ) : (Fin n → Bool) ≃ (Fin n → Bool) :=
  (signFlip_involutive a).toPerm (signFlip a)

/-- A "cross edge" in the $k$-partite hypergraph on $\mathrm{Fin}\,k \times \mathrm{Fin}\,n$:
a $k$-element set $e$ that picks exactly one vertex from each "part"
$\{i\} \times \mathrm{Fin}\,n$. -/
def IsCrossEdge {k n : ℕ} (e : Finset (Fin k × Fin n)) : Prop :=
  e.card = k ∧ ∀ i : Fin k, (e.filter (fun p => p.1 = i)).card = 1

/-- Discrepancy of a coloring on $k$-subsets of $S$: the signed sum
$\sum_{e \in \binom{S}{k}} \mathrm{color}(e)$ viewed as a real number. -/
noncomputable def discrepancy {k n : ℕ} (color : Finset (Fin k × Fin n) → ℤ)
    (S : Finset (Fin k × Fin n)) : ℝ :=
  ∑ e ∈ Finset.powersetCard k S, (color e : ℝ)

/-- **Improved unbalancing lights (Theorem 2.5.2).** For each $k \geq 2$ there is a
constant $c > 0$ such that for every $n \geq 1$ and every $\pm 1$ coloring of the
$k$-element subsets of $\mathrm{Fin}\,k \times \mathrm{Fin}\,n$ that assigns $+1$ to all
cross edges, some sub-hypergraph $S$ has discrepancy at least $c \cdot n^k$ in absolute
value. -/
end UnbalancingLights
