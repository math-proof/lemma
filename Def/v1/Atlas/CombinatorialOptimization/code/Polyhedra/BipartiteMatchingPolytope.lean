/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Polyhedra/BipartiteMatchingPolytope.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Lemma.Finset.Atlas.v1.CombinatorialOptimization.code.Polyhedra.BipartiteIncidenceTU
import Lemma.Finset.Atlas.v1.CombinatorialOptimization.code.Polyhedra.IntegralVertex
import Def.v1.Atlas.CombinatorialOptimization.code.Matching.MatchingCharacterization
import Lemma.Finset.Atlas.v1.CombinatorialOptimization.code.Matching.MatchingCharacterization
open SimpleGraph Finset Matrix


namespace BipartiteMatchingPolytope

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def IsMatchingSet (M : Set (Sym2 V)) : Prop :=
  M ⊆ G.edgeSet ∧ ∀ e₁ ∈ M, ∀ e₂ ∈ M, ∀ v : V, v ∈ e₁ → v ∈ e₂ → e₁ = e₂

def matchingLPRelaxation : Set (Sym2 V → ℝ) :=
  {x | (∀ e, 0 ≤ x e) ∧ (∀ v : V, ∑ e ∈ G.incidenceFinset v, x e ≤ 1) ∧
    (∀ e, e ∉ G.edgeFinset → x e = 0)}

def matchingIndicators : Set (Sym2 V → ℝ) :=
  {x | ∃ M : Finset (Sym2 V), ↑M ⊆ G.edgeSet ∧
    (∀ e₁ ∈ M, ∀ e₂ ∈ M, ∀ v : V, v ∈ e₁ → v ∈ e₂ → e₁ = e₂) ∧
    x = fun e => if e ∈ M then 1 else 0}

end BipartiteMatchingPolytope
