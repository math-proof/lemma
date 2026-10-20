/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SetFamily/IndependentSet.lean -/

import Mathlib.Data.Finset.Card
import sympy.atlas.Combinatorics.SetFamily.UniformHypergraph
/-!
# Independent sets and Steiner triple systems in finite hypergraphs

Shared set-family API: a vertex set is independent when no hyperedge is
fully contained in it, and a Steiner triple system is a 3-uniform family
in which every pair of distinct vertices lies in a unique edge.
-/

namespace SetFamily

variable {V : Type*}

/-- A vertex finset `I` is independent in `H` when no edge of `H` is fully
contained in `I`. -/
def IsIndependent (H : Finset (Finset V)) (I : Finset V) : Prop :=
  ∀ e ∈ H, ¬ e ⊆ I

/-- Unfolding lemma for `IsIndependent`. -/
theorem isIndependent_iff (H : Finset (Finset V)) (I : Finset V) :
    IsIndependent H I ↔ ∀ e ∈ H, ¬ e ⊆ I :=
  Iff.rfl

/-- Every vertex set is independent in the empty hypergraph. -/
theorem isIndependent_empty_hypergraph (I : Finset V) :
    IsIndependent (∅ : Finset (Finset V)) I := by
  simp [IsIndependent]

/-- Independence persists to subsets of the independent set. -/
theorem isIndependent_of_subset {H : Finset (Finset V)} {I J : Finset V}
    (h : IsIndependent H I) (hJI : J ⊆ I) : IsIndependent H J := by
  intro e he hsub
  exact h e he (hsub.trans hJI)

/-- The empty vertex set is independent iff every edge is nonempty. -/
theorem isIndependent_empty_iff (H : Finset (Finset V)) :
    IsIndependent H ∅ ↔ ∀ e ∈ H, e.Nonempty := by
  simp [IsIndependent, Finset.subset_empty, Finset.nonempty_iff_ne_empty]

/-- An `n`-vertex triple system modelled as a finset of unordered triples:
every edge has cardinality three, and every pair of distinct vertices lies
in exactly one edge of `H`. -/
def IsSteinerTripleSystem (H : Finset (Finset V)) : Prop :=
  IsUniform H 3 ∧
    ∀ u v : V, u ≠ v → ∃! e : Finset V, e ∈ H ∧ u ∈ e ∧ v ∈ e

/-- Uniformity projection from a Steiner triple system. -/
theorem uniform_of_isSteinerTripleSystem {H : Finset (Finset V)}
    (h : IsSteinerTripleSystem H) : IsUniform H 3 :=
  h.1

/-- Unique pair coverage from a Steiner triple system. -/
theorem pairCover_of_isSteinerTripleSystem {H : Finset (Finset V)}
    (h : IsSteinerTripleSystem H) :
    ∀ u v : V, u ≠ v → ∃! e : Finset V, e ∈ H ∧ u ∈ e ∧ v ∈ e :=
  h.2

/-- Unique membership in a singleton family: when the only edge satisfies `P`,
it is the unique edge satisfying `P`. -/
theorem existsUnique_mem_singleton {t : Finset V} {P : Finset V → Prop}
    (hP : P t) : ∃! e : Finset V, e ∈ ({t} : Finset (Finset V)) ∧ P e :=
  ⟨t, ⟨Finset.mem_singleton_self t, hP⟩,
    fun _e he => Finset.mem_singleton.mp he.1⟩

end SetFamily
