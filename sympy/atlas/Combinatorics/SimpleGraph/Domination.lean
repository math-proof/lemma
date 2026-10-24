/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Domination.lean -/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Order.Lattice.Nat

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
