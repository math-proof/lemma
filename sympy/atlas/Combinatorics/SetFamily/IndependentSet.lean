/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SetFamily/IndependentSet.lean -/

import Mathlib.Data.Finset.Card
import sympy.atlas.Combinatorics.SetFamily.UniformHypergraph
import Lemma.Finset.SetFamily.UniformHypergraph
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

/-- An `n`-vertex triple system modelled as a finset of unordered triples:
every edge has cardinality three, and every pair of distinct vertices lies
in exactly one edge of `H`. -/
def IsSteinerTripleSystem (H : Finset (Finset V)) : Prop :=
  IsUniform H 3 ∧
    ∀ u v : V, u ≠ v → ∃! e : Finset V, e ∈ H ∧ u ∈ e ∧ v ∈ e
end SetFamily
