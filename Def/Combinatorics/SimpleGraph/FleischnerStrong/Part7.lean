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
public import Theorem.Combinatorics.SimpleGraph.FleischnerStrong.Part3


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

attribute [instance] ComponentTrailCover.edge_finite

noncomputable def cycleCoverIncidenceEquiv [DecidableEq V]
    {c : G.Walk x x} (D : c.outsideGraph.ConnectedComponent)
    {p : (G.contractOutside (c.componentVertices D)).square.Walk none none}
    (hp : p.IsHamiltonianCycle)
    (hfirst : (G.contractOutside (c.componentVertices D)).Adj none p.snd)
    (hlast : (G.contractOutside (c.componentVertices D)).Adj p.penultimate none)
    (d : c.componentVertices D) :
    p.toSubgraph.spanningCoe.incidenceSet (some d) ≃
      {e : NontrivialCoverEdge p //
        (d : V) ∈ nontrivialCoverEnds D hp hfirst hlast e} where
  toFun := cycleIncidenceToCover D hp hfirst hlast d
  invFun := coverIncidenceToCycle D hp hfirst hlast d
  left_inv := coverIncidenceToCycle_cycleIncidenceToCover D hp hfirst hlast d
  right_inv := cycleIncidenceToCover_coverIncidenceToCycle D hp hfirst hlast d

def cycleCoverEdgeOfMem {S : Set V}
    (p : (G.contractOutside S).square.Walk none none) {a b : Option S}
    (he : s(a, b) ∈ p.edges) : CycleCoverEdge p := by
  refine ⟨s(a, b), ?_⟩
  change s(a, b) ∈ p.toSubgraph.spanningCoe.edgeSet
  rw [Subgraph.edgeSet_spanningCoe, p.mem_edges_toSubgraph]
  exact he

end Walk
end SimpleGraph
