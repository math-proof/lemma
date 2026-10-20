/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Clique.lean -/

/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.ENat.Lattice
import Mathlib.Order.CompletePartialOrder

namespace SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

open Finset List

@[inherit_doc] scoped notation "α(" G ")" => indepNum G

@[simp] lemma indepNum_of_isEmpty [IsEmpty V] : α(G) = 0 := by
  simp [indepNum, isNIndepSet_iff, Subsingleton.elim _ ∅]

@[simp] lemma indepNum_pos [Finite V] [Nonempty V] : 0 < α(G) := by
  cases nonempty_fintype V
  obtain ⟨v⟩ := ‹Nonempty V›
  rw [← Nat.add_one_le_iff]
  exact le_csSup ⟨Nat.card V, by simp [mem_upperBounds, isNIndepSet_iff, Finset.card_le_univ]⟩
    ⟨{v}, by simp [isNIndepSet_iff]⟩

/-- Infinite graphs: definitions for clique number so that the clique number of a graph
with unbounded clique size is `∞` rather than 0.
-/
noncomputable
def ecliqueNum (G : SimpleGraph V) : ℕ∞ := ⨆ (s : Finset V) (_ : G.IsClique s), #s

/-- The set of sizes of the inclusion-maximal finite cliques of `G` among finite
cliques. An infinite maximal clique is not represented. -/
def maximalCliqueSizes (G : SimpleGraph V) : Set ℕ :=
  { k | ∃ S : Finset V, Maximal (fun T : Finset V => G.IsClique (T : Set V)) S ∧ S.card = k }

open scoped Classical in
/-- The triangles of `G` containing the edge `uv`, that is, the `3`-cliques of `G` whose vertex
set contains both endpoints of `uv`. -/
noncomputable def trianglesContaining {α : Type*} [Fintype α] (G : SimpleGraph α)
    (uv : G.edgeSet) : Finset (Finset α) :=
  (G.cliqueFinset 3).filter (fun t ↦ uv.1.toFinset ⊆ t)

end SimpleGraph
