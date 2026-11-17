/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/IsogenyVolcano.lean -/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Structure.Combinatorics.IsogenyVolcano

@[expose] public section

set_option autoImplicit false

open BigOperators

/-!
# Isogeny volcanoes on multigraphs

This file defines symmetric multigraphs by edge multiplicity and the combinatorial structure of
an isogeny volcano. Loops are permitted. The degree counts a loop's multiplicity once, following
the outgoing-isogeny convention rather than the convention where an undirected loop counts twice.
-/


namespace Multigraph

variable {V : Type*}

/-- Adjacency in a multigraph means positive edge multiplicity. -/
def Adj (G : Multigraph V) (v w : V) : Prop :=
  0 < G.edgeMult v w

/--
The outgoing degree of a vertex. A loop contributes its multiplicity once, matching the
outgoing-isogeny convention.
-/
def degree (G : Multigraph V) [Fintype V] (v : V) : ℕ :=
  ∑ w : V, G.edgeMult v w

/-- Degree restricted to vertices satisfying `P`. -/
def degreeOn (G : Multigraph V) [Fintype V] (v : V)
    (P : V → Prop) [DecidablePred P] : ℕ :=
  ∑ w ∈ Finset.univ.filter P, G.edgeMult v w

/-- Connectivity via reflexive-transitive closure. -/
def Connected (G : Multigraph V) (v w : V) : Prop :=
  Relation.ReflTransGen G.Adj v w

/-- A multigraph is connected when all pairs connect. -/
def IsConnected (G : Multigraph V) : Prop :=
  ∀ v w, G.Connected v w

end Multigraph
