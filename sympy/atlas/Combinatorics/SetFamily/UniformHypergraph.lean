/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SetFamily/UniformHypergraph.lean -/

import Mathlib.Data.Finset.Powerset

/-!
# Uniform finite set families

This file provides shared predicates for finite set families used as finite
simple hypergraphs.

The API is adapted from
`google-deepmind/formal-conjectures@62f56e8e4dab933a720f649721875c478b0ecf1c`,
`FormalConjecturesForMathlib/Combinatorics/SetFamily/UniformHypergraph.lean`.
-/

namespace SetFamily

/-- A finite hypergraph is `r`-uniform when every edge has cardinality `r`. -/
def IsUniform {V : Type*} (H : Finset (Finset V)) (r : ℕ) : Prop :=
  ∀ e ∈ H, e.card = r

/-- Some `m` vertices contain at least `k` edges of `H`. -/
def ContainsSubgraph {V : Type*} [DecidableEq V]
    (H : Finset (Finset V)) (m k : ℕ) : Prop :=
  ∃ S : Finset V, S.card = m ∧
    k ≤ (H.filter fun e => e ⊆ S).card

/-- Unfolding characterization of uniformity. -/
theorem isUniform_iff {V : Type*} (H : Finset (Finset V)) (r : ℕ) :
    IsUniform H r ↔ ∀ e ∈ H, e.card = r :=
  Iff.rfl

/-- Unfolding characterization of finite subhypergraph containment. -/
theorem containsSubgraph_iff {V : Type*} [DecidableEq V]
    (H : Finset (Finset V)) (m k : ℕ) :
    ContainsSubgraph H m k ↔
      ∃ S : Finset V, S.card = m ∧ k ≤ (H.filter fun e => e ⊆ S).card :=
  Iff.rfl

end SetFamily
