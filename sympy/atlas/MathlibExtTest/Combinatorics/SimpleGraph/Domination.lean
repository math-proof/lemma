/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/Domination.lean -/


import sympy.atlas.Combinatorics.SimpleGraph.Domination
import Lemma.SimpleGraph.Domination

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- The universal set dominates every graph. -/
example : G.IsDominating Set.univ := fun v => Or.inl (Set.mem_univ v)

/-- An independent dominating set is independent and dominating. -/
example {S : Set V} (h : G.IsIndepDominating S) : G.IsIndepSet S := h.1
example {S : Set V} (h : G.IsIndepDominating S) : G.IsDominating S := h.2

/-- The invariant is attained by an independent dominating finset. -/
example [Fintype V] :
    ∃ S : Finset V, S.card = G.indepDominationNumber ∧ G.IsIndepDominating ↑S :=
  G.exists_indepDominationNumber_eq_card

/-- Every independent dominating finset bounds the invariant from below. -/
example [Fintype V] {S : Finset V} (hS : G.IsIndepDominating ↑S) :
    G.indepDominationNumber ≤ S.card :=
  G.indepDominationNumber_le_card hS

/-- The domination number is attained by a dominating finset. -/
example [Fintype V] :
    ∃ S : Finset V, S.card = G.dominationNumber ∧ G.IsDominating ↑S :=
  G.exists_dominationNumber_eq_card

/-- Every dominating finset bounds the invariant from below. -/
example [Fintype V] {S : Finset V} (hS : G.IsDominating ↑S) :
    G.dominationNumber ≤ S.card :=
  G.dominationNumber_le_card hS

end SimpleGraph
