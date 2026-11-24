module
public import Def.Combinatorics.SimpleGraph.StrongSquareCycle
public import Theorem.SimpleGraph.StrongSquareCycle
public import Theorem.SimpleGraph.VertexConnectivity
public import Theorem.SimpleGraph.Contraction
public import Theorem.SimpleGraph.EdgeIndexedMultigraph
public import Theorem.SimpleGraph.Riha
public import Theorem.Combinatorics.SimpleGraph.VertexConnectivity
public import Theorem.Combinatorics.SimpleGraph.Contraction.Part3
public import Def.Combinatorics.SimpleGraph.EdgeIndexedMultigraph.Part4
public import Def.Combinatorics.SimpleGraph.Riha
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Basic.Finite.Sigma
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Data.List.ChainOfFn
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.List.NodupEquivFin
public import Mathlib.Data.ZMod.Basic
public import Def.Combinatorics.SimpleGraph.FleischnerStrong.Part8


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
/-!
# The strengthened Fleischner theorem

This file proves the vertex-rooted form of Fleischner's theorem: the square has a Hamiltonian
cycle whose two edges at a prescribed vertex are edges of the original graph.

The proof-specific component, trail, transition, Euler-circuit, and marking constructions are
private to this module.
-/
/-! ## CycleComplement -/
namespace SimpleGraph

namespace Walk

universe u

variable {V : Type u} {G : SimpleGraph V} {x : V}

theorem component_eq_outsideComponent (c : G.Walk x x)
    (D : c.outsideGraph.ConnectedComponent) {v : V} (hv : v ∉ c.support)
    (hvD : v ∈ c.componentVertices D) : outsideComponent c hv = D := by
  obtain ⟨hv', hD⟩ := (c.mem_componentVertices_iff D v).mp hvD
  simpa [outsideComponent] using hD

theorem mem_support_of_mem_cycle_edge (c : G.Walk x x)
    (i : Fin c.length) {v : V}
    (hv : v ∈ s(c.getVert i, c.getVert (i + 1))) : v ∈ c.support := by
  rcases Sym2.mem_iff.mp hv with rfl | rfl
  · exact c.getVert_mem_support i
  · exact c.getVert_mem_support (i + 1)

end Walk
end SimpleGraph
