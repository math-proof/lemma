/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter4/Triangles.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Instances.Real.Lemmas
set_option maxHeartbeats 800000

noncomputable section

open Filter Topology Finset BigOperators

namespace RandomGraph

/-- Linear index assigned to an unordered pair $\{a, b\}$ with $a < b$, given by
$\binom{b}{2} + a$. Used to enumerate edges of the complete graph $K_n$ as
elements of $\mathrm{Fin}\binom{n}{2}$. -/
def pairToEdgeIndex (a b : ℕ) : ℕ := Nat.choose b 2 + a

/-- The index of a pair with $a < b < n$ lies below $\binom{n}{2}$, ensuring that
`pairToEdgeIndex` produces a valid `Fin (Nat.choose n 2)`. -/
lemma pairToEdgeIndex_lt_choose {a b n : ℕ} (hab : a < b) (hbn : b < n) :
    pairToEdgeIndex a b < Nat.choose n 2 := by
  unfold pairToEdgeIndex
  have h1 : Nat.choose b 2 + a < Nat.choose b 2 + b := Nat.add_lt_add_left hab _
  have h2 : Nat.choose b 2 + b = Nat.choose (b + 1) 2 := by
    simp [Nat.choose_succ_succ, Nat.choose_one_right]; ring
  rw [h2] at h1
  exact lt_of_lt_of_le h1 (Nat.choose_le_choose 2 hbn)

/-- Edge index of the ordered pair $(i, j)$ with $i < j$ in $K_n$, as an element of
$\mathrm{Fin}\binom{n}{2}$. -/
def edgeIndex (n : ℕ) (i j : Fin n) (hij : i.val < j.val) : Fin (Nat.choose n 2) :=
  ⟨pairToEdgeIndex i.val j.val, pairToEdgeIndex_lt_choose hij j.isLt⟩

/-- Tests whether the edge $\{i, j\}$ is present according to the bit-vector $f$
encoding a graph on $n$ vertices; returns false unless $i < j$. -/
def edgePresent (n : ℕ) (f : Fin (Nat.choose n 2) → Bool) (i j : Fin n) : Bool :=
  if h : i.val < j.val then f (edgeIndex n i j h) else false

/-- Decides whether the graph on $n$ vertices encoded by $f$ contains a triangle, by
searching for an ordered triple $i < j < k$ with all three edges present. -/
def hasTriangle (n : ℕ) (f : Fin (Nat.choose n 2) → Bool) : Bool :=
  (Finset.univ.val : Multiset (Fin n × Fin n × Fin n)).toList.any fun ijk =>
    let i := ijk.1
    let j := ijk.2.1
    let k := ijk.2.2
    edgePresent n f i j && edgePresent n f i k && edgePresent n f j k &&
    decide (i.val < j.val) && decide (j.val < k.val)

/-- The probability that $G(n, p)$ contains a triangle, computed by summing the
indicator of `hasTriangle` weighted by the Bernoulli$(p)$ product weights over all
$2^{\binom{n}{2}}$ edge configurations. -/
def erdosRenyiTriangleProb (n : ℕ) (p : ℝ) : ℝ :=
  let m := Nat.choose n 2
  ∑ f : Fin m → Bool,
    (if hasTriangle n f then 1 else 0) *
    ∏ i : Fin m, (if f i then p else 1 - p)

/-- The expected number of triangles in $G(n, p)$, given by
$\mathbb{E}[X] = \binom{n}{3} p^3$ (Proposition 4.1.2). -/
noncomputable def expectedTriangles (n : ℕ) (p : ℝ) : ℝ :=
  (Nat.choose n 3 : ℝ) * p ^ 3
