/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter3/RandomGreedyColoring/StructuralLemma.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter1.TwoColorable.Part2
import Lemma.Finset.Atlas.v1.ProbabilisticMethodsInCombinatorics.code.Chapter1.TwoColorable
open Finset Fintype


namespace TwoColorableHypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `IsMaxIn σ v e` says that $v$ belongs to the edge $e$ and attains the maximum value of
the ordering $\sigma$ on $e$. -/
def IsMaxIn (σ : V → ℕ) (v : V) (e : Finset V) : Prop :=
  v ∈ e ∧ ∀ u ∈ e, σ u ≤ σ v

/-- `IsMinIn σ v e` says that $v$ belongs to the edge $e$ and attains the minimum value of
the ordering $\sigma$ on $e$. -/
def IsMinIn (σ : V → ℕ) (v : V) (e : Finset V) : Prop :=
  v ∈ e ∧ ∀ u ∈ e, σ v ≤ σ u

/-- A hypergraph $H$ has a *conflicting pair* under the ordering $\sigma$ if there are two
edges $e, f \in H$ and a vertex $v$ such that $v$ is the $\sigma$-maximum of $e$, the
$\sigma$-minimum of $f$, and $e \cap f = \{v\}$. -/
def HasConflictingPair (H : Hypergraph V) (σ : V → ℕ) : Prop :=
  ∃ e ∈ H, ∃ f ∈ H, ∃ v : V,
    IsMaxIn σ v e ∧ IsMinIn σ v f ∧ (e ∩ f = {v})

/-- The greedy 2-coloring induced by an injective ordering $\sigma$: process vertices in
increasing $\sigma$-order and color $v$ `false` if there is an edge $e \ni v$ whose other
vertices are smaller than $v$ and already colored `true`; otherwise color $v$ `true`. -/
noncomputable def greedyCol (σ : V → ℕ) (hσ : Function.Injective σ)
    (H : Hypergraph V) : V → Bool := by
  classical
  exact WellFounded.fix (InvImage.wf σ Nat.lt_wfRel.wf) fun v ih =>
    if ∃ e ∈ H, v ∈ e ∧ (∀ u ∈ e, σ u ≤ σ v) ∧
       (∀ u ∈ e, (hlt : σ u < σ v) → ih u hlt = true)
    then false
    else true

end TwoColorableHypergraph
