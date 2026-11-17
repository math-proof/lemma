/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Domination.lean -/

module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Order.Lattice.Nat

@[expose] public section

namespace SimpleGraph

/-- `S` dominates `G`: every vertex is in `S` or adjacent to a vertex of `S`. -/
def IsDominating {V : Type*} (G : SimpleGraph V) (S : Set V) : Prop :=
  ∀ v : V, v ∈ S ∨ ∃ u ∈ S, G.Adj u v

/-- `S` is an independent dominating set: independent and dominating. -/
def IsIndepDominating {V : Type*} (G : SimpleGraph V) (S : Set V) : Prop :=
  G.IsIndepSet S ∧ G.IsDominating S

/-- The domination number: the least size of a dominating set. -/
noncomputable def dominationNumber {V : Type*} (G : SimpleGraph V)
    [Fintype V] : ℕ :=
  sInf {k : ℕ | ∃ S : Finset V, S.card = k ∧ G.IsDominating ↑S}

/-- The independent domination number: the least size of an independent
dominating set. -/
noncomputable def indepDominationNumber {V : Type*} (G : SimpleGraph V)
    [Fintype V] : ℕ :=
  sInf {k : ℕ | ∃ S : Finset V, S.card = k ∧ G.IsIndepDominating ↑S}

end SimpleGraph
