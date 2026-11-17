/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/ChromaticNumber.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Find
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Tactic

@[expose] public section

namespace ChromaticNumber

open Finset Real Filter Nat Classical

/-- Expected number of $k$-cliques in $G(n,1/2)$:
$\mu = \binom{n}{k} \cdot 2^{-\binom{k}{2}}$. -/
noncomputable def muClique (n k : ℕ) : ℝ :=
  (Nat.choose n k : ℝ) * (2 : ℝ) ^ (-(Nat.choose k 2 : ℤ))

/-- The largest $k \le n$ for which the expected number $\mu(n,k)$ of $k$-cliques in
$G(n,1/2)$ is still at least $1$. -/
noncomputable def k₀ (n : ℕ) : ℕ :=
  Nat.findGreatest (fun k => (1 : ℝ) ≤ muClique n k) n

/-- Clique number of a finite graph on `Fin n`: the largest $k \le n$ such that $G$
contains a clique of size $k$. -/
noncomputable def cliqueNum {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  Nat.findGreatest (fun k => ¬G.CliqueFree k) n

/-- Probability of an event $A$ on graphs sampled from $G(n,1/2)$, computed combinatorially
as the fraction of graphs on $\{1,\dots,n\}$ satisfying $A$. -/
noncomputable def probGnHalf (n : ℕ) (A : SimpleGraph (Fin n) → Prop) : ℝ :=
  ((Finset.univ.filter (fun G => A G)).card : ℝ) /
  (Fintype.card (SimpleGraph (Fin n)) : ℝ)

/-- The $\Delta$ quantity from Janson's inequality applied to the $k$-clique event in
$G(n,1/2)$: a sum over the shared-vertex parameter $s \in [2, k-1]$ that bounds the
correlation between pairs of overlapping $k$-cliques. -/
noncomputable def deltaClique (n k : ℕ) : ℝ :=
  ∑ s ∈ Finset.Icc 2 (k - 1),
    (Nat.choose k s : ℝ) * (Nat.choose (n - k) (k - s) : ℝ) *
    (Nat.choose n k : ℝ) * (2 : ℝ) ^ (-(2 * Nat.choose k 2 - Nat.choose s 2 : ℤ))

end ChromaticNumber
