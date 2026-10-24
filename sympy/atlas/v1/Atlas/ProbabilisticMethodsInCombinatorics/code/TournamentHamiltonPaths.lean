/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/TournamentHamiltonPaths.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.LinearAlgebra.Matrix.Permanent
import sympy.atlas.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter10.Permanent
import Lemma.Finset.Atlas.v1.ProbabilisticMethodsInCombinatorics.code.Chapter10.Permanent
set_option maxHeartbeats 3200000

open Real Finset BigOperators

namespace TournamentHamiltonPaths

/-- A tournament on $n$ vertices: an irreflexive, complete, asymmetric directed-edge
relation on $\mathrm{Fin}\, n$, equipped with a decidability instance. -/
structure Tournament (n : ℕ) where
  edge : Fin n → Fin n → Prop
  irrefl : ∀ i, ¬ edge i i
  complete : ∀ i j, i ≠ j → (edge i j ∨ edge j i)
  antisymm : ∀ i j, edge i j → ¬ edge j i
  [decEdge : DecidableRel edge]

attribute [instance] Tournament.decEdge

/-- Number of Hamilton paths of $T$: permutations $\sigma$ of $\mathrm{Fin}\, n$ such that
every consecutive edge $\sigma(i) \to \sigma(i+1)$ lies in $T$. -/
noncomputable def Tournament.numHamiltonPaths {n : ℕ} (T : Tournament n) : ℕ := by
  classical
  exact (Finset.univ.filter fun σ : Equiv.Perm (Fin n) =>
    ∀ i : Fin n, (h : i.val + 1 < n) → T.edge (σ i) (σ ⟨i.val + 1, h⟩)).card

/-- Number of Hamilton cycles of $T$: permutations $\sigma$ of $\mathrm{Fin}(n+1)$ such
that every cyclic edge $\sigma(i) \to \sigma(i+1)$ lies in $T$; zero if $n = 0$. -/
noncomputable def Tournament.numHamiltonCycles {n : ℕ} (T : Tournament n) : ℕ := by
  classical
  exact match n, T with
  | 0, _ => 0
  | n + 1, T =>
    (Finset.univ.filter fun σ : Equiv.Perm (Fin (n + 1)) =>
      ∀ i : Fin (n + 1), T.edge (σ i) (σ (i + 1))).card

/-- Adjacency matrix of a tournament as a real $0/1$-matrix: entry $(i, j)$ is $1$ if
$T$ has the edge $i \to j$, else $0$. -/
noncomputable def Tournament.adjMatrix {n : ℕ} (T : Tournament n) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of (fun i j => if T.edge i j then (1 : ℝ) else 0)

/-- Successor permutation derived from $\sigma$: the conjugate $\sigma \circ (+1) \circ
\sigma^{-1}$, which sends $\sigma(j)$ to $\sigma(j + 1)$. -/
noncomputable def toSuccPerm {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    Equiv.Perm (Fin (n + 1)) :=
  σ * Equiv.addRight (1 : Fin (n + 1)) * σ⁻¹

@[simp] private lemma toSuccPerm_apply {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) (v : Fin (n + 1)) :
    toSuccPerm σ v = σ (σ⁻¹ v + 1) := by
  simp [toSuccPerm, Equiv.Perm.mul_apply, Equiv.addRight]
